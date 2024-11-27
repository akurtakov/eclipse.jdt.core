/*******************************************************************************
 * Copyright (c) 2000, 2019 IBM Corporation and others.
 *
 * This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License 2.0
 * which accompanies this distribution, and is available at
 * https://www.eclipse.org/legal/epl-2.0/
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/
package org.eclipse.jdt.internal.core.search.matching;

import static org.eclipse.jdt.internal.core.search.matching.DOMASTNodeUtils.insideDocComment;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.ISourceReference;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.core.dom.*;
import org.eclipse.jdt.core.dom.BreakStatement;
import org.eclipse.jdt.core.dom.LabeledStatement;
import org.eclipse.jdt.core.search.IJavaSearchConstants;
import org.eclipse.jdt.core.search.SearchMatch;
import org.eclipse.jdt.core.search.SearchPattern;
import org.eclipse.jdt.core.search.TypeDeclarationMatch;
import org.eclipse.jdt.core.search.TypeReferenceMatch;
import org.eclipse.jdt.internal.compiler.ast.*;
import org.eclipse.jdt.internal.compiler.ast.ASTNode;
import org.eclipse.jdt.internal.compiler.ast.Annotation;
import org.eclipse.jdt.internal.compiler.ast.Expression;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.env.IBinaryType;
import org.eclipse.jdt.internal.compiler.lookup.*;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.VariableBinding;
import org.eclipse.jdt.internal.compiler.util.SimpleSet;
import org.eclipse.jdt.internal.core.JavaElement;

public class TypeReferenceLocator extends PatternLocator {

protected final TypeReferencePattern pattern;
protected final boolean isDeclarationOfReferencedTypesPattern;

private final int fineGrain;
private final Map<QualifiedTypeReference, List<TypeBinding>> recordedResolutions = new HashMap<>();
private List<IJavaElement> foundElements = new ArrayList<>();

public TypeReferenceLocator(TypeReferencePattern pattern) {

	super(pattern);

	this.pattern = pattern;
	this.fineGrain = pattern == null ? 0 : pattern.fineGrain;
	this.isDeclarationOfReferencedTypesPattern = this.pattern instanceof DeclarationOfReferencedTypesPattern;
}
@Override
protected void clear() {
	this.recordedResolutions.clear();
}
protected IJavaElement findElement(IJavaElement element, int accuracy) {
	// need exact match to be able to open on type ref
	if (accuracy != SearchMatch.A_ACCURATE) return null;

	// element that references the type must be included in the enclosing element
	DeclarationOfReferencedTypesPattern declPattern = (DeclarationOfReferencedTypesPattern) this.pattern;
	while (element != null && !declPattern.enclosingElement.equals(element))
		element = element.getParent();
	return element;
}
@Override
protected int fineGrain() {
	return this.fineGrain;
}
@Override
public int match(Annotation node, MatchingNodeSet nodeSet) {
	return match(node.type, nodeSet);
}
@Override
public int match(org.eclipse.jdt.core.dom.Annotation node, MatchingNodeSet nodeSet, MatchLocator locator) {
	return match(node.getTypeName(), nodeSet, locator);
}
@Override
public int match(ASTNode node, MatchingNodeSet nodeSet) { // interested in ImportReference
	if (!(node instanceof ImportReference)) return IMPOSSIBLE_MATCH;

	return nodeSet.addMatch(node, matchLevel((ImportReference) node));
}
//public int match(ConstructorDeclaration node, MatchingNodeSet nodeSet) - SKIP IT
//public int match(Expression node, MatchingNodeSet nodeSet) - SKIP IT
//public int match(FieldDeclaration node, MatchingNodeSet nodeSet) - SKIP IT
//public int match(MethodDeclaration node, MatchingNodeSet nodeSet) - SKIP IT
//public int match(MessageSend node, MatchingNodeSet nodeSet) - SKIP IT
@Override
public int match(Reference node, MatchingNodeSet nodeSet) { // interested in NameReference & its subtypes
	if (!(node instanceof NameReference)) return IMPOSSIBLE_MATCH;

	if (this.pattern.simpleName == null)
		return nodeSet.addMatch(node, this.pattern.mustResolve ? POSSIBLE_MATCH : ACCURATE_MATCH);

	if (node instanceof SingleNameReference) {
		if (matchesName(this.pattern.simpleName, ((SingleNameReference) node).token))
			return nodeSet.addMatch(node, POSSIBLE_MATCH); // resolution is needed to find out if it is a type ref
	} else {
		char[][] tokens = ((QualifiedNameReference) node).tokens;
		for (char[] token : tokens)
			if (matchesName(this.pattern.simpleName, token))
				return nodeSet.addMatch(node, POSSIBLE_MATCH); // resolution is needed to find out if it is a type ref
	}

	return IMPOSSIBLE_MATCH;
}
@Override
public int match(Name name, MatchingNodeSet nodeSet, MatchLocator locator) {
	if (name.getParent() instanceof AbstractTypeDeclaration) {
		return IMPOSSIBLE_MATCH;
	}
	if( name.getParent() instanceof LabeledStatement ls && ls.getLabel() == name) {
		return IMPOSSIBLE_MATCH;
	}
	if( name.getParent() instanceof BreakStatement bs && bs.getLabel() == name) {
		return IMPOSSIBLE_MATCH;
	}
	if (this.pattern.simpleName == null) {
		return nodeSet.addMatch(name, this.pattern.mustResolve ? POSSIBLE_MATCH : ACCURATE_MATCH);
	}
	if( name instanceof SimpleName sn2 ) {
		if( this.pattern.qualification == null)
			return match(sn2, nodeSet);
		// searching for a qualified name but we are only simple
		org.eclipse.jdt.core.dom.ASTNode parent3 = name.getParent();
		if( !(parent3 instanceof QualifiedName)) {
			return match(sn2, nodeSet);
		}
		// Parent is a qualified name and we didn't match it...
		// so we know the whole name was a failed match, but...
		if( parent3 instanceof QualifiedName qn3 && qn3.getQualifier() == name) {
			// Maybe the qualifier is the type we're looking for
			if( match(sn2, nodeSet) == POSSIBLE_MATCH) {
				return POSSIBLE_MATCH;
			}
		}

		if( this.pattern.getMatchMode() == SearchPattern.R_EXACT_MATCH) {
			return IMPOSSIBLE_MATCH;
		}
		if( match(sn2, nodeSet) == POSSIBLE_MATCH) {
			return POSSIBLE_MATCH;
		}
		return IMPOSSIBLE_MATCH;
	}
	if( name instanceof QualifiedName qn2 ) {
		return match(qn2, nodeSet);
	}
	return IMPOSSIBLE_MATCH;
}

public int match(SimpleName name, MatchingNodeSet nodeSet) {
	String simpleName = name.getIdentifier();
	return simpleName != null && matchesName(this.pattern.simpleName, simpleName.toCharArray()) ?
		POSSIBLE_MATCH : IMPOSSIBLE_MATCH;
}
public int match(QualifiedName name, MatchingNodeSet nodeSet) {
	String simpleName = name.getName().getIdentifier();
	String qualifier = name.getQualifier().toString();
	if( this.pattern.qualification == null ) {
		// Return an impossible match here, because we are not seeking a qualifier.
		// The SimpleName node should be the one to respond.
		return IMPOSSIBLE_MATCH;
	}
	if( qualifier != null) {
		String desiredQualifier = new String(this.pattern.qualification);
		if( !qualifier.equals(desiredQualifier)) {
			return IMPOSSIBLE_MATCH;
		}
	}
	return simpleName != null && matchesName(this.pattern.simpleName, simpleName.toCharArray()) ?
		POSSIBLE_MATCH : IMPOSSIBLE_MATCH;
}
//public int match(TypeDeclaration node, MatchingNodeSet nodeSet) - SKIP IT
@Override
public int match(TypeReference node, MatchingNodeSet nodeSet) {
	if (this.pattern.simpleName == null)
		return nodeSet.addMatch(node, this.pattern.mustResolve ? POSSIBLE_MATCH : ACCURATE_MATCH);

	if (node instanceof SingleTypeReference) {
		if (matchesName(this.pattern.simpleName, ((SingleTypeReference) node).token))
			return nodeSet.addMatch(node, this.pattern.mustResolve ? POSSIBLE_MATCH : ACCURATE_MATCH);
	} else {
		char[][] tokens = ((QualifiedTypeReference) node).tokens;
		for (char[] token : tokens)
			if (matchesName(this.pattern.simpleName, token))
				return nodeSet.addMatch(node, POSSIBLE_MATCH); // resolution is needed to find out if it is a type ref
	}

	return IMPOSSIBLE_MATCH;
}
@Override
public int match(org.eclipse.jdt.core.dom.ASTNode node, MatchingNodeSet nodeSet, MatchLocator locator) {
	if (node instanceof EnumConstantDeclaration enumConstantDecl
		&& node.getParent() instanceof EnumDeclaration enumDeclaration
		&& enumConstantDecl.getAnonymousClassDeclaration() != null) {
		if (this.pattern.simpleName == null) {
			return nodeSet.addMatch(node, this.pattern.mustResolve ? POSSIBLE_MATCH : ACCURATE_MATCH);
		}
		if (matchesName(this.pattern.simpleName, enumDeclaration.getName().getIdentifier().toCharArray())) {
			return nodeSet.addMatch(node, this.pattern.mustResolve ? POSSIBLE_MATCH : ACCURATE_MATCH);
		}
	}
	return IMPOSSIBLE_MATCH;
}
@Override
public int match(Type node, MatchingNodeSet nodeSet, MatchLocator locator) {
	if (this.pattern.simpleName == null)
		return nodeSet.addMatch(node, this.pattern.mustResolve ? POSSIBLE_MATCH : ACCURATE_MATCH);
	String qualifiedName = null;
	String simpleName = null;
	if (node instanceof SimpleType simple) {
		if (simple.getName() instanceof SimpleName name) {
			simpleName = name.getIdentifier();
		}
		if (simple.getName() instanceof QualifiedName name) {
			simpleName = name.getName().getIdentifier();
			qualifiedName = name.getFullyQualifiedName();
		}
	} else if (node instanceof QualifiedType qualified) {
		simpleName = qualified.getName().getIdentifier();
		qualifiedName = qualified.getName().getFullyQualifiedName();
	}
	if( qualifiedName != null && this.pattern.qualification != null) {
		// we have a qualified name in the node, and our pattern is searching for a qualified name
		char[] patternQualified = (new String(this.pattern.qualification) + "." + new String(this.pattern.simpleName)).toCharArray();
		char[] found = qualifiedName.toCharArray();
		if( matchesName(patternQualified, found)) {
			return nodeSet.addMatch(node, this.pattern.mustResolve ? POSSIBLE_MATCH : ACCURATE_MATCH);
		}
	} else if (simpleName != null && matchesName(this.pattern.simpleName, simpleName.toCharArray())) {
		return nodeSet.addMatch(node, this.pattern.mustResolve || this.pattern.qualification == null ? POSSIBLE_MATCH : ACCURATE_MATCH);
	}
	return IMPOSSIBLE_MATCH;
}

@Override
protected int matchLevel(ImportReference importRef) {
	if (this.pattern.qualification == null) {
		if (this.pattern.simpleName == null) return ACCURATE_MATCH;
		char[][] tokens = importRef.tokens;
		boolean onDemand = (importRef.bits & ASTNode.OnDemand) != 0;
		final boolean isStatic = importRef.isStatic();
		if (!isStatic && onDemand) {
			return IMPOSSIBLE_MATCH;
		}
		int length = tokens.length;
		if (matchesName(this.pattern.simpleName, tokens[length-1])) {
			return ACCURATE_MATCH;
		}
		if (isStatic && !onDemand && length > 1) {
			if (matchesName(this.pattern.simpleName, tokens[length-2])) {
				return ACCURATE_MATCH;
			}
		}
	} else {
		char[][] tokens = importRef.tokens;
		char[] qualifiedPattern = this.pattern.simpleName == null
			? this.pattern.qualification
			: CharOperation.concat(this.pattern.qualification, this.pattern.simpleName, '.');
		char[] qualifiedTypeName = CharOperation.concatWith(tokens, '.');
		if (qualifiedPattern == null) return ACCURATE_MATCH; // null is as if it was "*"
		if (qualifiedTypeName == null) return IMPOSSIBLE_MATCH; // cannot match null name
		if (qualifiedTypeName.length == 0) { // empty name
			if (qualifiedPattern.length == 0) { // can only matches empty pattern
				return ACCURATE_MATCH;
			}
			return IMPOSSIBLE_MATCH;
		}
		boolean matchFirstChar = !this.isCaseSensitive || (qualifiedPattern[0] == qualifiedTypeName[0]);
		switch (this.matchMode) {
			case SearchPattern.R_EXACT_MATCH:
			case SearchPattern.R_PREFIX_MATCH:
				if (CharOperation.prefixEquals(qualifiedPattern, qualifiedTypeName, this.isCaseSensitive)) {
					return POSSIBLE_MATCH;
				}
				break;

			case SearchPattern.R_PATTERN_MATCH:
				if (CharOperation.match(qualifiedPattern, qualifiedTypeName, this.isCaseSensitive)) {
					return POSSIBLE_MATCH;
				}
				break;

			case SearchPattern.R_REGEXP_MATCH :
				// TODO (frederic) implement regular expression match
				break;
			case SearchPattern.R_CAMELCASE_MATCH:
				if (matchFirstChar && CharOperation.camelCaseMatch(qualifiedPattern, qualifiedTypeName, false)) {
					return POSSIBLE_MATCH;
				}
				// only test case insensitive as CamelCase already verified prefix case sensitive
				if (!this.isCaseSensitive && CharOperation.prefixEquals(qualifiedPattern, qualifiedTypeName, false)) {
					return POSSIBLE_MATCH;
				}
				break;
			case SearchPattern.R_CAMELCASE_SAME_PART_COUNT_MATCH:
				if (matchFirstChar && CharOperation.camelCaseMatch(qualifiedPattern, qualifiedTypeName, true)) {
					return POSSIBLE_MATCH;
				}
				break;
		}
	}
	return IMPOSSIBLE_MATCH;
}

@Override
protected void matchLevelAndReportImportRef(ImportReference importRef, Binding binding, MatchLocator locator) throws CoreException {
	Binding refBinding = binding;
	if (importRef.isStatic()) {
		// for static import, binding can be a field binding or a member type binding
		// verify that in this case binding is static and use declaring class for fields
		if (binding instanceof FieldBinding) {
			FieldBinding fieldBinding = (FieldBinding) binding;
			if (!fieldBinding.isStatic()) return;
			refBinding = fieldBinding.declaringClass;
		} else if (binding instanceof MethodBinding) {
			MethodBinding methodBinding = (MethodBinding) binding;
			if (!methodBinding.isStatic()) return;
			refBinding = methodBinding.declaringClass;
		} else if (binding instanceof MemberTypeBinding) {
			MemberTypeBinding memberBinding = (MemberTypeBinding) binding;
			if (!memberBinding.isStatic()) return;
		}
		// resolve and report
		int level = resolveLevel(refBinding);
		if (level >= INACCURATE_MATCH) {
			matchReportImportRef(
				importRef,
				binding,
				locator.createImportHandle(importRef),
				level == ACCURATE_MATCH
					? SearchMatch.A_ACCURATE
					: SearchMatch.A_INACCURATE,
				locator);
		}
		return;
	}
	super.matchLevelAndReportImportRef(importRef, refBinding, locator);
}
@Override
protected void matchReportImportRef(ImportReference importRef, Binding binding, IJavaElement element, int accuracy, MatchLocator locator) throws CoreException {
	if (this.isDeclarationOfReferencedTypesPattern) {
		if ((element = findElement(element, accuracy)) != null) {
			SimpleSet knownTypes = ((DeclarationOfReferencedTypesPattern) this.pattern).knownTypes;
			while (binding instanceof ReferenceBinding) {
				ReferenceBinding typeBinding = (ReferenceBinding) binding;
				reportDeclaration(typeBinding, 1, locator, knownTypes);
				binding = typeBinding.enclosingType();
			}
		}
		return;
	}

	// return if this is not necessary to report
	if (this.pattern.hasTypeArguments() && !this.isEquivalentMatch &&!this.isErasureMatch) {
		return;
	}

	// Return if fine grain is on and does not concern import reference
	if ((this.pattern.fineGrain != 0 && (this.pattern.fineGrain & IJavaSearchConstants.IMPORT_DECLARATION_TYPE_REFERENCE) == 0)) {
		return;
	}

	// Create search match
	this.match = locator.newTypeReferenceMatch(element, binding, accuracy, importRef);

	// set match raw flag and rule
	this.match.setRaw(true);
	if (this.pattern.hasTypeArguments()) {
		// binding is raw => only compatible erasure if pattern has type arguments
		this.match.setRule(this.match.getRule() & (~SearchPattern.R_FULL_MATCH));
	}

	// Try to find best selection for match
	TypeBinding typeBinding = null;
	boolean lastButOne = false;
	if (binding instanceof ReferenceBinding) {
		typeBinding = (ReferenceBinding) binding;
	} else if (binding instanceof FieldBinding) { // may happen for static import
		typeBinding = ((FieldBinding)binding).declaringClass;
		lastButOne = importRef.isStatic() && ((importRef.bits & ASTNode.OnDemand) == 0);
	} else if (binding instanceof MethodBinding) { // may happen for static import
		typeBinding = ((MethodBinding)binding).declaringClass;
		lastButOne = importRef.isStatic() && ((importRef.bits & ASTNode.OnDemand) == 0);
	}
	if (typeBinding != null) {
		int lastIndex = importRef.tokens.length - 1;
		if (lastButOne) {
			// for field or method static import, use last but one token
			lastIndex--;
		}
		if (typeBinding instanceof ProblemReferenceBinding) {
			ProblemReferenceBinding pbBinding = (ProblemReferenceBinding) typeBinding;
			typeBinding = pbBinding.closestMatch();
			lastIndex = pbBinding.compoundName.length - 1;
		}
		// try to match all enclosing types for which the token matches as well.
		while (typeBinding != null && lastIndex >= 0) {
			if (resolveLevelForType(typeBinding) != IMPOSSIBLE_MATCH) {
				if (locator.encloses(element)) {
					long[] positions = importRef.sourcePositions;
					// index now depends on pattern type signature
					int index = lastIndex;
					if (this.pattern.qualification != null) {
						index = lastIndex - this.pattern.segmentsSize;
					}
					if (index < 0) index = 0;
					int start = (int) ((positions[index]) >>> 32);
					int end = (int) positions[lastIndex];
					// report match
					this.match.setOffset(start);
					this.match.setLength(end-start+1);
					locator.report(this.match);
				}
				return;
			}
			lastIndex--;
			typeBinding = typeBinding.enclosingType();
		}
	}
	locator.reportAccurateTypeReference(this.match, importRef, this.pattern.simpleName);
}
protected void matchReportReference(ArrayTypeReference arrayRef, IJavaElement element, Binding elementBinding, int accuracy, MatchLocator locator) throws CoreException {
	if (this.pattern.simpleName == null) {
		// TODO (frederic) need to add a test for this case while searching generic types...
		if (locator.encloses(element)) {
			int offset = arrayRef.sourceStart;
			int length = arrayRef.sourceEnd-offset+1;
			if (this.match == null) {
				this.match = locator.newTypeReferenceMatch(element, elementBinding, accuracy, offset, length, arrayRef);
			} else {
				this.match.setOffset(offset);
				this.match.setLength(length);
			}
			locator.report(this.match);
			return;
		}
	}
	this.match = locator.newTypeReferenceMatch(element, elementBinding, accuracy, arrayRef);
	if (arrayRef.resolvedType != null) {
		matchReportReference(arrayRef, -1, arrayRef.resolvedType.leafComponentType(), locator);
		return;
	}
	locator.reportAccurateTypeReference(this.match, arrayRef, this.pattern.simpleName);
}
/**
 * Reports the match of the given reference.
 */
@Override
protected void matchReportReference(ASTNode reference, IJavaElement element, Binding elementBinding, int accuracy, MatchLocator locator) throws CoreException {
	matchReportReference(reference, element, null, null, elementBinding, accuracy, locator);
}
/**
 * Reports the match of the given reference. Also provide a local and other elements to eventually report in match.
 */
@Override
protected void matchReportReference(ASTNode reference, IJavaElement element, IJavaElement localElement, IJavaElement[] otherElements, Binding elementBinding, int accuracy, MatchLocator locator) throws CoreException {
	if (this.isDeclarationOfReferencedTypesPattern) {
		if ((element = findElement(element, accuracy)) != null)
			reportDeclaration(reference, element, locator, ((DeclarationOfReferencedTypesPattern) this.pattern).knownTypes);
		return;
	}

	// Create search match
	TypeReferenceMatch refMatch = locator.newTypeReferenceMatch(element, elementBinding, accuracy, reference);
	refMatch.setLocalElement(localElement);
	refMatch.setOtherElements(otherElements);
	this.match = refMatch;

	// Report match depending on reference type
	if (reference instanceof QualifiedNameReference)
		matchReportReference((QualifiedNameReference) reference, element, elementBinding, accuracy, locator);
	else if (reference instanceof QualifiedTypeReference)
		matchReportReference((QualifiedTypeReference) reference, element, elementBinding, accuracy, locator);
	else if (reference instanceof ArrayTypeReference)
		matchReportReference((ArrayTypeReference) reference, element, elementBinding, accuracy, locator);
	else {
		TypeBinding typeBinding = reference instanceof Expression  &&
				((org.eclipse.jdt.internal.compiler.ast.Expression) reference).isTrulyExpression() ?
						((Expression)reference).resolvedType : null;
		if (typeBinding != null) {
			matchReportReference((Expression)reference, -1, typeBinding, locator);
			return;
		}
		locator.report(this.match);
	}
}
protected void matchReportReference(QualifiedNameReference qNameRef, IJavaElement element, Binding elementBinding, int accuracy, MatchLocator locator) throws CoreException {
	Binding binding = qNameRef.binding;
	TypeBinding typeBinding = null;
	int lastIndex = qNameRef.tokens.length - 1;
	switch (qNameRef.bits & ASTNode.RestrictiveFlagMASK) {
		case Binding.FIELD : // reading a field
			typeBinding = qNameRef.actualReceiverType;
			lastIndex -= qNameRef.otherBindings == null ? 1 : qNameRef.otherBindings.length + 1;
			break;
		case Binding.TYPE : //=============only type ==============
			if (binding instanceof TypeBinding)
				typeBinding = (TypeBinding) binding;
			break;
		case Binding.VARIABLE : //============unbound cases===========
		case Binding.TYPE | Binding.VARIABLE :
			if (binding instanceof ProblemReferenceBinding) {
				typeBinding = (TypeBinding) binding;
			} else if (binding instanceof ProblemFieldBinding) {
				typeBinding = qNameRef.actualReceiverType;
				lastIndex -= qNameRef.otherBindings == null ? 1 : qNameRef.otherBindings.length + 1;
			} else if (binding instanceof ProblemBinding) {
				typeBinding = ((ProblemBinding) binding).searchType;
			}
			break;
	}
	if (typeBinding instanceof ProblemReferenceBinding) {
		ProblemReferenceBinding pbBinding = (ProblemReferenceBinding) typeBinding;
		typeBinding = pbBinding.closestMatch();
		lastIndex = pbBinding.compoundName.length - 1;
	}

	// Create search match to report
	if (this.match == null) {
		this.match = locator.newTypeReferenceMatch(element, elementBinding, accuracy, qNameRef);
	}

	// try to match all enclosing types for which the token matches as well.
	if (typeBinding instanceof ReferenceBinding) {
		ReferenceBinding refBinding = (ReferenceBinding) typeBinding;
		while (refBinding != null && lastIndex >= 0) {
			if (resolveLevelForType(refBinding) == ACCURATE_MATCH) {
				if (locator.encloses(element)) {
					long[] positions = qNameRef.sourcePositions;
					// index now depends on pattern type signature
					int index = lastIndex;
					if (this.pattern.qualification != null) {
						index = lastIndex - this.pattern.segmentsSize;
					}
					if (index < 0) index = 0;
					int start = (int) ((positions[index]) >>> 32);
					int end = (int) positions[lastIndex];
					this.match.setOffset(start);
					this.match.setLength(end-start+1);

					//  Look if there's a need to special report for parameterized type
					matchReportReference(qNameRef, lastIndex, refBinding, locator);
				}
				return;
			}
			lastIndex--;
			refBinding = refBinding.enclosingType();
		}
	}
	locator.reportAccurateTypeReference(this.match, qNameRef, this.pattern.simpleName);
}
protected void matchReportReference(QualifiedTypeReference qTypeRef, IJavaElement element, Binding elementBinding, int accuracy, MatchLocator locator) throws CoreException {
	TypeBinding typeBinding = qTypeRef.resolvedType;
	int lastIndex = qTypeRef.tokens.length - 1;
	if (typeBinding instanceof ArrayBinding)
		typeBinding = ((ArrayBinding) typeBinding).leafComponentType;
	if (typeBinding instanceof ProblemReferenceBinding) {
		ProblemReferenceBinding pbBinding = (ProblemReferenceBinding) typeBinding;
		typeBinding = pbBinding.closestMatch();
		lastIndex = pbBinding.compoundName.length - 1;
	}

	// Create search match to report
	if (this.match == null) {
		this.match = locator.newTypeReferenceMatch(element, elementBinding, accuracy, qTypeRef);
	}

	// try to match all enclosing types for which the token matches as well
	if (typeBinding instanceof ReferenceBinding) {
		ReferenceBinding refBinding = (ReferenceBinding) typeBinding;
		while (refBinding != null && lastIndex >= 0) {
			if (resolveLevelForType(refBinding) != IMPOSSIBLE_MATCH) {
				if (locator.encloses(element)) {
					long[] positions = qTypeRef.sourcePositions;
					// index now depends on pattern type signature
					int index = lastIndex;
					if (this.pattern.qualification != null) {
						index = lastIndex - this.pattern.segmentsSize;
					}
					if (index < 0) index = 0;
					int start = (int) ((positions[index]) >>> 32);
					int end = (int) positions[lastIndex];
					this.match.setOffset(start);
					this.match.setLength(end-start+1);

					//  Look if there's a need to special report for parameterized type
					matchReportReference(qTypeRef, lastIndex, refBinding, locator);
				}
				return;
			}
			lastIndex--;
			refBinding = refBinding.enclosingType();
		}
	}
	locator.reportAccurateTypeReference(this.match, qTypeRef, this.pattern.simpleName);
}
void matchReportReference(Expression expr, int lastIndex, TypeBinding refBinding, MatchLocator locator) throws CoreException {

	// Look if there's a need to special report for parameterized type
	if (refBinding.isParameterizedType() || refBinding.isRawType()) {

		// Try to refine accuracy
		ParameterizedTypeBinding parameterizedBinding = (ParameterizedTypeBinding)refBinding;
		updateMatch(parameterizedBinding, this.pattern.getTypeArguments(), this.pattern.hasTypeParameters(), 0, locator);

		// See whether it is necessary to report or not
		if (this.match.getRule() == 0) return; // impossible match
		boolean report = (this.isErasureMatch && this.match.isErasure()) || (this.isEquivalentMatch && this.match.isEquivalent()) || this.match.isExact();
		if (!report) return;

		// Make a special report for parameterized types if necessary
		 if (refBinding.isParameterizedType() && this.pattern.hasTypeArguments())  {
			TypeReference typeRef = null;
			TypeReference[] typeArguments = null;
			if (expr instanceof ParameterizedQualifiedTypeReference) {
				typeRef = (ParameterizedQualifiedTypeReference) expr;
				typeArguments = ((ParameterizedQualifiedTypeReference) expr).typeArguments[lastIndex];
			}
			else if (expr instanceof ParameterizedSingleTypeReference) {
				typeRef = (ParameterizedSingleTypeReference) expr;
				typeArguments = ((ParameterizedSingleTypeReference) expr).typeArguments;
			}
			if (typeRef != null) {
				locator.reportAccurateParameterizedTypeReference(this.match, typeRef, lastIndex, typeArguments);
				return;
			}
		}
	} else if (this.pattern.hasTypeArguments()) { // binding has no type params, compatible erasure if pattern does
		this.match.setRule(SearchPattern.R_ERASURE_MATCH);
	}

	// Report match
	if (expr instanceof ArrayTypeReference) {
		locator.reportAccurateTypeReference(this.match, expr, this.pattern.simpleName);
		return;
	}
	if (refBinding.isLocalType()) {
		// see bug https://bugs.eclipse.org/bugs/show_bug.cgi?id=82673
		LocalTypeBinding local = (LocalTypeBinding) refBinding.erasure();
		IJavaElement focus = this.pattern.focus;
		if (focus != null && local.enclosingMethod != null && focus.getParent().getElementType() == IJavaElement.METHOD) {
			IMethod method = (IMethod) focus.getParent();
			if (!CharOperation.equals(local.enclosingMethod.selector, method.getElementName().toCharArray())) {
				return;
			}
		}
	}
	if (this.pattern.simpleName == null) {
		this.match.setOffset(expr.sourceStart);
		this.match.setLength(expr.sourceEnd-expr.sourceStart+1);
	}
	locator.report(this.match);
}
@Override
protected int referenceType() {
	return IJavaElement.TYPE;
}
protected void reportDeclaration(ASTNode reference, IJavaElement element, MatchLocator locator, SimpleSet knownTypes) throws CoreException {
	int maxType = -1;
	TypeBinding typeBinding = null;
	if (reference instanceof TypeReference) {
		typeBinding = ((TypeReference) reference).resolvedType;
		maxType = Integer.MAX_VALUE;
	} else if (reference instanceof QualifiedNameReference) {
		QualifiedNameReference qNameRef = (QualifiedNameReference) reference;
		Binding binding = qNameRef.binding;
		maxType = qNameRef.tokens.length - 1;
		switch (qNameRef.bits & ASTNode.RestrictiveFlagMASK) {
			case Binding.FIELD : // reading a field
				typeBinding = qNameRef.actualReceiverType;
				maxType -= qNameRef.otherBindings == null ? 1 : qNameRef.otherBindings.length + 1;
				break;
			case Binding.TYPE : //=============only type ==============
				if (binding instanceof TypeBinding)
					typeBinding = (TypeBinding) binding;
				break;
			case Binding.VARIABLE : //============unbound cases===========
			case Binding.TYPE | Binding.VARIABLE :
				if (binding instanceof ProblemFieldBinding) {
					typeBinding = qNameRef.actualReceiverType;
					maxType -= qNameRef.otherBindings == null ? 1 : qNameRef.otherBindings.length + 1;
				} else if (binding instanceof ProblemBinding) {
					ProblemBinding pbBinding = (ProblemBinding) binding;
					typeBinding = pbBinding.searchType; // second chance with recorded type so far
					char[] partialQualifiedName = pbBinding.name;
					maxType = CharOperation.occurencesOf('.', partialQualifiedName) - 1; // index of last bound token is one before the pb token
					if (typeBinding == null || maxType < 0) return;
				}
				break;
		}
	} else if (reference instanceof SingleNameReference) {
		typeBinding = (TypeBinding) ((SingleNameReference) reference).binding;
		maxType = 1;
	}

	if (typeBinding instanceof ArrayBinding)
		typeBinding = ((ArrayBinding) typeBinding).leafComponentType;
	if (typeBinding == null || typeBinding instanceof BaseTypeBinding) return;
	if (typeBinding instanceof ProblemReferenceBinding) {
		TypeBinding original = typeBinding.closestMatch();
		if (original == null) return; // original may not be set (bug 71279)
		typeBinding = original;
	}
	typeBinding = typeBinding.erasure();
	reportDeclaration((ReferenceBinding) typeBinding, maxType, locator, knownTypes);
}
protected void reportDeclaration(ReferenceBinding typeBinding, int maxType, MatchLocator locator, SimpleSet knownTypes) throws CoreException {
	IType type = locator.lookupType(typeBinding);
	if (type == null) return; // case of a secondary type

	IResource resource = type.getResource();
	boolean isBinary = type.isBinary();
	IBinaryType info = null;
	if (isBinary) {
		if (resource == null)
			resource = type.getJavaProject().getProject();
		info = locator.getBinaryInfo((org.eclipse.jdt.internal.core.ClassFile) type.getClassFile(), resource);
	}
	while (maxType >= 0 && type != null) {
		if (!knownTypes.includes(type)) {
			if (isBinary) {
				locator.reportBinaryMemberDeclaration(resource, type, typeBinding, info, SearchMatch.A_ACCURATE);
			} else {
				if (typeBinding instanceof ParameterizedTypeBinding)
					typeBinding = ((ParameterizedTypeBinding) typeBinding).genericType();
				ClassScope scope = ((SourceTypeBinding) typeBinding).scope;
				if (scope != null) {
					TypeDeclaration typeDecl = scope.referenceContext;
					int offset = typeDecl.sourceStart;
					this.match = new TypeDeclarationMatch(((JavaElement) type).resolved(typeBinding), SearchMatch.A_ACCURATE, offset, typeDecl.sourceEnd-offset+1, locator.getParticipant(), resource);
					locator.report(this.match);
				}
			}
			knownTypes.add(type);
		}
		typeBinding = typeBinding.enclosingType();
		IJavaElement parent = type.getParent();
		if (parent instanceof IType) {
			type = (IType)parent;
		} else {
			type = null;
		}
		maxType--;
	}
}
@Override
public int resolveLevel(ASTNode node) {
	if (node instanceof TypeReference)
		return resolveLevel((TypeReference) node);
	if (node instanceof NameReference)
		return resolveLevel((NameReference) node);
//	if (node instanceof ImportReference) - Not called when resolve is true, see MatchingNodeSet.reportMatching(unit)
	return IMPOSSIBLE_MATCH;
}
@Override
public int resolveLevel(Binding binding) {
	if (binding == null) return INACCURATE_MATCH;

	if(binding instanceof MethodBinding)
		return resolveLevel((MethodBinding) binding);
	if(binding instanceof VariableBinding)
		return resolveLevel((VariableBinding) binding);

	if (!(binding instanceof TypeBinding)) return IMPOSSIBLE_MATCH;

	TypeBinding typeBinding = (TypeBinding) binding;
	if (typeBinding instanceof ArrayBinding)
		typeBinding = ((ArrayBinding) typeBinding).leafComponentType;
	if (typeBinding instanceof ProblemReferenceBinding)
		typeBinding = ((ProblemReferenceBinding) typeBinding).closestMatch();

	return resolveLevelForTypeOrEnclosingTypes(this.pattern.simpleName, this.pattern.qualification, typeBinding);
}
private int resolveLevel(MethodBinding binding) {
	int level = resolveLevelForTypes(binding.parameters);
	if(level != IMPOSSIBLE_MATCH) {
		return level;
	}

	if(binding.typeVariables != null) {
		for (TypeVariableBinding tv : binding.typeVariables) {
			if(tv.superclass != null) {
				level = resolveLevelForType(tv.superclass);
				if(level != IMPOSSIBLE_MATCH) {
					return level;
				}
			}

			level = resolveLevelForTypes(tv.superInterfaces);
			if(level != IMPOSSIBLE_MATCH) {
				return level;
			}
		}
	}

	if(!binding.isVoidMethod() && binding.returnType != null) {
		return resolveLevelForType(binding.returnType);
	}

	return IMPOSSIBLE_MATCH;
}
private int resolveLevel(VariableBinding binding) {
	if(binding.type != null) {
		return resolveLevelForType(binding.type);
	}
	return IMPOSSIBLE_MATCH;
}
private int resolveLevelForTypes(TypeBinding[] types) {
	if(types != null) {
		for (TypeBinding t : types) {
			int levelForType = resolveLevelForType(t);
			if(levelForType != IMPOSSIBLE_MATCH) {
				return levelForType;
			}
		}
	}
	return IMPOSSIBLE_MATCH;
}
protected int resolveLevel(NameReference nameRef) {
	Binding binding = nameRef.binding;

	if (nameRef instanceof SingleNameReference) {
		if (binding instanceof ProblemReferenceBinding)
			binding = ((ProblemReferenceBinding) binding).closestMatch();
		if (binding instanceof ReferenceBinding)
			return resolveLevelForType((ReferenceBinding) binding);
		if (((SingleNameReference) nameRef).isLabel)
			return IMPOSSIBLE_MATCH;

		return binding == null || binding instanceof ProblemBinding ? INACCURATE_MATCH : IMPOSSIBLE_MATCH;
	}

	TypeBinding typeBinding = null;
	QualifiedNameReference qNameRef = (QualifiedNameReference) nameRef;
	switch (qNameRef.bits & ASTNode.RestrictiveFlagMASK) {
		case Binding.FIELD : // reading a field
			if (qNameRef.tokens.length < (qNameRef.otherBindings == null ? 2 : qNameRef.otherBindings.length + 2))
				return IMPOSSIBLE_MATCH; // must be at least A.x
			typeBinding = nameRef.actualReceiverType;
			break;
		case Binding.LOCAL : // reading a local variable
			return IMPOSSIBLE_MATCH; // no type match in it
		case Binding.TYPE : //=============only type ==============
			if (binding instanceof TypeBinding)
				typeBinding = (TypeBinding) binding;
			break;
		/*
		 * Handling of unbound qualified name references. The match may reside in the resolved fragment,
		 * which is recorded inside the problem binding, along with the portion of the name until it became a problem.
		 */
		case Binding.VARIABLE : //============unbound cases===========
		case Binding.TYPE | Binding.VARIABLE :
			if (binding instanceof ProblemReferenceBinding) {
				typeBinding = (TypeBinding) binding;
			} else if (binding instanceof ProblemFieldBinding) {
				if (qNameRef.tokens.length < (qNameRef.otherBindings == null ? 2 : qNameRef.otherBindings.length + 2))
					return IMPOSSIBLE_MATCH; // must be at least A.x
				typeBinding = nameRef.actualReceiverType;
			} else if (binding instanceof ProblemBinding) {
				ProblemBinding pbBinding = (ProblemBinding) binding;
				if (CharOperation.occurencesOf('.', pbBinding.name) <= 0) // index of last bound token is one before the pb token
					return INACCURATE_MATCH;
				typeBinding = pbBinding.searchType;
			}
			break;
	}
	return resolveLevel(typeBinding);
}
protected int resolveLevel(TypeReference typeRef) {
	TypeBinding typeBinding = typeRef.resolvedType;
	if (typeBinding instanceof ArrayBinding)
		typeBinding = ((ArrayBinding) typeBinding).leafComponentType;
	if (typeBinding instanceof ProblemReferenceBinding)
		typeBinding = ((ProblemReferenceBinding) typeBinding).closestMatch();

	if (typeRef instanceof SingleTypeReference) {
		return resolveLevelForType(typeBinding);
	} else
		return resolveLevelForTypeOrQualifyingTypes(typeRef, typeBinding);
}
/* (non-Javadoc)
 * Resolve level for type with a given binding.
 * This is just an helper to avoid call of method with all parameters...
 */
protected int resolveLevelForType(TypeBinding typeBinding) {
	if (typeBinding == null || !typeBinding.isValidBinding()) {
		if (this.pattern.typeSuffix != TYPE_SUFFIX) return INACCURATE_MATCH;
	} else {
		switch (this.pattern.typeSuffix) {
			case CLASS_SUFFIX:
				if (!typeBinding.isClass()) return IMPOSSIBLE_MATCH;
				break;
			case CLASS_AND_INTERFACE_SUFFIX:
				if (!(typeBinding.isClass() || (typeBinding.isInterface() && !typeBinding.isAnnotationType()))) return IMPOSSIBLE_MATCH;
				break;
			case CLASS_AND_ENUM_SUFFIX:
				if (!(typeBinding.isClass() || typeBinding.isEnum())) return IMPOSSIBLE_MATCH;
				break;
			case INTERFACE_SUFFIX:
				if (!typeBinding.isInterface() || typeBinding.isAnnotationType()) return IMPOSSIBLE_MATCH;
				break;
			case INTERFACE_AND_ANNOTATION_SUFFIX:
				if (!(typeBinding.isInterface() || typeBinding.isAnnotationType())) return IMPOSSIBLE_MATCH;
				break;
			case ENUM_SUFFIX:
				if (!typeBinding.isEnum()) return IMPOSSIBLE_MATCH;
				break;
			case ANNOTATION_TYPE_SUFFIX:
				if (!typeBinding.isAnnotationType()) return IMPOSSIBLE_MATCH;
				break;
			case TYPE_SUFFIX : // nothing
		}
	}
	return resolveLevelForType( this.pattern.simpleName,
						this.pattern.qualification,
						this.pattern.getTypeArguments(),
						0,
						typeBinding);
}
protected int resolveLevelForType(ITypeBinding typeBinding) {
	if (typeBinding == null) {
		if (this.pattern.typeSuffix != TYPE_SUFFIX) return INACCURATE_MATCH;
	} else {
		switch (this.pattern.typeSuffix) {
			case CLASS_SUFFIX:
				if (!typeBinding.isClass()) return IMPOSSIBLE_MATCH;
				break;
			case CLASS_AND_INTERFACE_SUFFIX:
				if (!(typeBinding.isClass() || (typeBinding.isInterface() && !typeBinding.isAnnotation()))) return IMPOSSIBLE_MATCH;
				break;
			case CLASS_AND_ENUM_SUFFIX:
				if (!(typeBinding.isClass() || typeBinding.isEnum())) return IMPOSSIBLE_MATCH;
				break;
			case INTERFACE_SUFFIX:
				if (!typeBinding.isInterface() || typeBinding.isAnnotation()) return IMPOSSIBLE_MATCH;
				break;
			case INTERFACE_AND_ANNOTATION_SUFFIX:
				if (!(typeBinding.isInterface() || typeBinding.isAnnotation())) return IMPOSSIBLE_MATCH;
				break;
			case ENUM_SUFFIX:
				if (!typeBinding.isEnum()) return IMPOSSIBLE_MATCH;
				break;
			case ANNOTATION_TYPE_SUFFIX:
				if (!typeBinding.isAnnotation()) return IMPOSSIBLE_MATCH;
				break;
			case TYPE_SUFFIX : // nothing
		}
	}
	return resolveLevelForType(this.pattern.simpleName,
						this.pattern.qualification,
						typeBinding);
}
/**
 * Returns whether the given type binding or one of its enclosing types
 * matches the given simple name pattern and qualification pattern.
 * Returns ACCURATE_MATCH if it does.
 * Returns INACCURATE_MATCH if resolve failed.
 * Returns IMPOSSIBLE_MATCH if it doesn't.
 */
protected int resolveLevelForTypeOrEnclosingTypes(char[] simpleNamePattern, char[] qualificationPattern, TypeBinding binding) {
	if (binding == null) return INACCURATE_MATCH;

	if (binding instanceof ReferenceBinding) {
		ReferenceBinding type = (ReferenceBinding) binding;
		while (type != null) {
			int level = resolveLevelForType(type);
			if (level != IMPOSSIBLE_MATCH) return level;

			type = type.enclosingType();
		}
	}
	return IMPOSSIBLE_MATCH;
}

int resolveLevelForTypeOrQualifyingTypes(TypeReference typeRef, TypeBinding typeBinding) {
	if (typeBinding == null || !typeBinding.isValidBinding()) return INACCURATE_MATCH;
	List<TypeBinding> resolutionsList = this.recordedResolutions.get(typeRef);
	if (resolutionsList != null) {
		for (TypeBinding resolution : resolutionsList) {
			int level = resolveLevelForType(resolution);
			if (level != IMPOSSIBLE_MATCH) return level;
		}
	}
	return IMPOSSIBLE_MATCH;
}
@Override
public void recordResolution(QualifiedTypeReference typeReference, TypeBinding resolution) {
	List<TypeBinding> resolutionsForTypeReference = this.recordedResolutions.get(typeReference);
	if (resolutionsForTypeReference == null) {
		resolutionsForTypeReference = new ArrayList<>();
	}
	resolutionsForTypeReference.add(resolution);
	this.recordedResolutions.put(typeReference, resolutionsForTypeReference);
}
@Override
public String toString() {
	return "Locator for " + this.pattern.toString(); //$NON-NLS-1$
}

private boolean hasPackageDeclarationAncestor(org.eclipse.jdt.core.dom.ASTNode node) {
	if( node instanceof PackageDeclaration) {
		return true;
	}
	return node == null ? false : hasPackageDeclarationAncestor(node.getParent());
}

@Override
public int resolveLevel(org.eclipse.jdt.core.dom.ASTNode node, IBinding binding, MatchLocator locator) {
	if (binding == null) {
		if( node instanceof SimpleName sn) {
			int accuracy = resolveLevelForSimpleName(node, sn.getIdentifier());
			if( accuracy != -1 ) {
				// Add directly
				IResource r = null;
				IJavaElement enclosing = DOMASTNodeUtils.getEnclosingJavaElement(node);
				IJavaElement ancestor = enclosing == null ? null : enclosing.getAncestor(IJavaElement.COMPILATION_UNIT);
				try {
					r = ancestor == null ? null : ancestor.getCorrespondingResource();
				} catch(JavaModelException jme) {
					// ignore
				}

				TypeReferenceMatch typeMatch = new TypeReferenceMatch(enclosing, accuracy, node.getStartPosition(), node.getLength(), insideDocComment(node), locator.getParticipant(), r);
				try {
					locator.report(typeMatch);
				} catch(CoreException ce) {
					// ignore
				}
				// Then return not possible so it doesn't get added again
				return IMPOSSIBLE_MATCH;
			}
		}
		return INACCURATE_MATCH;
	}
	if (binding instanceof ITypeBinding typeBinding) {
		return resolveLevelForTypeBinding(node, typeBinding, locator);
	}
	if( binding instanceof IPackageBinding && node instanceof SimpleName sn) {
		// var x = (B36479.C)val;
		// might interpret the B36479 to be a package and C a type,
		// rather than B36479 to be a type and C to be an inner-type
		if( this.isDeclarationOfReferencedTypesPattern) {
			return IMPOSSIBLE_MATCH;
		}
		if( hasPackageDeclarationAncestor(node)) {
			return IMPOSSIBLE_MATCH;
		}
		String identifier = sn.getIdentifier();
		if( matchesName(this.pattern.simpleName, identifier.toCharArray())) {
			return INACCURATE_MATCH;
		}

	}
	return IMPOSSIBLE_MATCH;
}

/*
 * Returns a match flag OR -1 if it cannot determine at all.
 */
private int resolveLevelForSimpleName(org.eclipse.jdt.core.dom.ASTNode node, String simpleNameNeedle) {
	if( !simpleNameNeedle.contains(".") && this.pattern.qualification != null && this.pattern.qualification.length > 0 ) { //$NON-NLS-1$
		// we need to find out if we import this thing at all
		org.eclipse.jdt.core.dom.CompilationUnit cu = findCU(node);
		List imports = cu.imports();
		for( Object id : imports) {
			ImportDeclaration idd = (ImportDeclaration)id;
			if( idd.getName() instanceof QualifiedName qn) {
				if( qn.getName().toString().equals(simpleNameNeedle)) {
					char[] qualifiedPattern = getQualifiedPattern(this.pattern.simpleName, this.pattern.qualification);
					// we were imported as qualified name...
					int level3 = resolveLevelForTypeSourceName(qualifiedPattern, qn.toString().toCharArray(), null);
					if( level3 == ACCURATE_MATCH ) {
						return INACCURATE_MATCH;
					}
					return INACCURATE_MATCH;
				}
			}
		}
	}
	return -1;
}

private int resolveLevelForTypeBinding(org.eclipse.jdt.core.dom.ASTNode node, ITypeBinding typeBinding,
		MatchLocator locator) {
	int newLevel = resolveLevelForType(this.pattern.simpleName, this.pattern.qualification, typeBinding);
	if( newLevel == IMPOSSIBLE_MATCH ) {
		String qualNameFromBinding = typeBinding.getQualifiedName();
		int simpleNameMatch = resolveLevelForSimpleName(node, qualNameFromBinding);
		if( simpleNameMatch != -1 ) {
			return simpleNameMatch;
		}
	}
	if( this.isDeclarationOfReferencedTypesPattern) {
		IJavaElement enclosing = ((DeclarationOfReferencedTypesPattern)this.pattern).enclosingElement;
		// We don't add this node. We manually add the declaration
		ITypeBinding t2 = typeBinding.getTypeDeclaration();
		IJavaElement je = t2 == null ? null : t2.getJavaElement();
		if( je != null && !this.foundElements.contains(je) && DOMASTNodeUtils.isWithinRange(node, enclosing)) {
			ISourceReference sr = je instanceof ISourceReference ? (ISourceReference)je : null;
			IResource r = null;
			ISourceRange srg = null;
			ISourceRange nameRange = null;
			try {
				srg = sr.getSourceRange();
				nameRange = sr.getNameRange();
				IJavaElement ancestor = je.getAncestor(IJavaElement.COMPILATION_UNIT);
				r = ancestor == null ? null : ancestor.getCorrespondingResource();
			} catch(JavaModelException jme) {
				// ignore
			}
			ISourceRange rangeToUse = (nameRange == null) ? srg : nameRange;
			if( rangeToUse != null ) {
				TypeDeclarationMatch tdm = new TypeDeclarationMatch(je, newLevel,
						rangeToUse.getOffset(), rangeToUse.getLength(),
						locator.getParticipant(), r);
				try {
					this.foundElements.add(je);
					locator.report(tdm);
				} catch(CoreException ce) {
					// ignore
				}
			}
		}
		return IMPOSSIBLE_MATCH;
	}
	return newLevel;
}

private org.eclipse.jdt.core.dom.CompilationUnit findCU(org.eclipse.jdt.core.dom.ASTNode node) {
	if( node == null )
		return null;
	if( node instanceof org.eclipse.jdt.core.dom.CompilationUnit cu) {
		return cu;
	}
	return findCU(node.getParent());
}

}
