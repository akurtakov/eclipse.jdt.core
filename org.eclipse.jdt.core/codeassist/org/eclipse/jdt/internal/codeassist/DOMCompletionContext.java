/*******************************************************************************
 * Copyright (c) 2024 Red Hat, Inc. and others.
 *
 * This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License 2.0
 * which accompanies this distribution, and is available at
 * https://www.eclipse.org/legal/epl-2.0/
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 * Contributors:
 *     Gayan Perera - initial API and implementation
 *******************************************************************************/
package org.eclipse.jdt.internal.codeassist;

import java.util.Optional;
import java.util.function.Supplier;
import java.util.stream.Stream;
import org.eclipse.jdt.core.CompletionContext;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.Signature;
import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.core.dom.*;

class DOMCompletionContext extends CompletionContext {
	private final int offset;
	private final char[] token;
	private final IJavaElement enclosingElement;
	private final Supplier<Stream<IBinding>> bindingsAcquirer;
	private final ExpectedTypes expectedTypes;
	private boolean inJavadoc = false;
	private final ASTNode node;

	DOMCompletionContext(int offset, char[] token, IJavaElement enclosingElement,
			Supplier<Stream<IBinding>> bindingHaver, ExpectedTypes expectedTypes, ASTNode node) {
		this.offset = offset;
		this.enclosingElement = enclosingElement;
		this.token = token;
		this.bindingsAcquirer = bindingHaver;
		this.expectedTypes = expectedTypes;
		this.node = node;
	}

	@Override
	public int getOffset() {
		return this.offset;
	}

	@Override
	public char[] getToken() {
		return this.token;
	}

	@Override
	public boolean isInJavadoc() {
		return this.inJavadoc;
	}

	public void setInJavadoc(boolean inJavadoc) {
		this.inJavadoc = inJavadoc;
	}

	@Override
	public IJavaElement getEnclosingElement() {
		return this.enclosingElement;
	}

	@Override
	public IJavaElement[] getVisibleElements(String typeSignature) {
		return this.bindingsAcquirer.get() //
			.filter(binding -> matchesSignature(binding, typeSignature)) //
			.map(binding -> binding.getJavaElement()) //
			.filter(obj -> obj != null) // eg. ArrayList.getFirst() when working with a Java 8 project
			.toArray(IJavaElement[]::new);
	}

	/// Checks if the binding matches the given type signature
	/// TODO: this should probably live in a helper method/utils class,
	/// along with `castCompatable`
	public static boolean matchesSignature(IBinding binding, String typeSignature) {
		if (typeSignature == null) {
			return binding instanceof IVariableBinding || binding instanceof IMethodBinding;
		}
		if (binding instanceof IVariableBinding variableBinding) {
			return castCompatable(variableBinding.getType(),
					typeSignature);
		} else if (binding instanceof IMethodBinding methodBinding) {
			return castCompatable(methodBinding.getReturnType(),
					typeSignature);
		}
		// notably, ITypeBinding is not used to complete values,
		// even, for instance, in the case that a `java.lang.Class<?>` is desired.
		return false;
	}

	@Override
	public char[][] getExpectedTypesKeys() {
		return this.expectedTypes.getExpectedTypes().stream() //
				.map(ITypeBinding::getKey) //
				.map(String::toCharArray) //
				.toArray(char[][]::new);
	}

	@Override
	public boolean isExtended() {
		return true;
	}

	@Override
	public int getTokenLocation() {
		ASTNode parent = this.node;
		while (parent != null) {
			if (parent instanceof ImportDeclaration) {
				return TL_IN_IMPORT;
			}
			parent = parent.getParent();
		}
		if (this.node.getParent() instanceof FieldAccess
			|| this.node.getParent() instanceof QualifiedName) {
			return 0;
		}
		if (this.node.getParent() instanceof VariableDeclaration) {
			return 0;
		}
		if (this.node instanceof AbstractTypeDeclaration) {
			return TL_MEMBER_START;
		}
		var locationInParent = node.getLocationInParent();
		parent = node;
		while (parent != null) {
			if (parent instanceof ClassInstanceCreation) {
				return TL_CONSTRUCTOR_START;
			}
			if (parent instanceof Block) {
				return TL_STATEMENT_START;
			}
			if (locationInParent == AnnotationTypeDeclaration.BODY_DECLARATIONS_PROPERTY ||
				locationInParent == EnumDeclaration.BODY_DECLARATIONS_PROPERTY ||
				locationInParent == ImplicitTypeDeclaration.BODY_DECLARATIONS_PROPERTY ||
				locationInParent == RecordDeclaration.BODY_DECLARATIONS_PROPERTY ||
				locationInParent == TypeDeclaration.BODY_DECLARATIONS_PROPERTY ||
				locationInParent == AnonymousClassDeclaration.BODY_DECLARATIONS_PROPERTY) {
				return TL_MEMBER_START;
			}
			if (parent instanceof FieldAccess) {
				return 0;
			}
			if (parent instanceof VariableDeclaration) {
				return 0;
			}
			locationInParent = parent.getLocationInParent();
			parent = parent.getParent();
		}
		return 0;
	}

	@Override
	public int getTokenStart() {
		if (node instanceof SimpleName) {
			return node.getStartPosition();
		}
		return this.offset;
	}
	@Override
	public int getTokenEnd() {
		if (node instanceof SimpleName) {
			return node.getStartPosition() + node.getLength() - 1;
		}
		return getTokenStart() + token.length - 1;
	}

	@Override
	public int getTokenKind() {
		return node instanceof StringLiteral ? TOKEN_KIND_STRING_LITERAL : TOKEN_KIND_NAME;
	}

	/// adapted from org.eclipse.jdt.internal.codeassist.InternalExtendedCompletionContext
	public boolean canUseDiamond(String[] parameterTypes, char[][] typeVariables) {
		// If no LHS or return type expected, then we can safely use diamond
		char[][] expectedTypekeys = this.getExpectedTypesKeys();
		if (expectedTypekeys == null || expectedTypekeys.length == 0)
			return true;
		// Next, find out whether any of the constructor parameters are the same as one of the
		// class type variables. If yes, diamond cannot be used.
		if (typeVariables != null) {
			for (String parameterType : parameterTypes) {
				for (char[] typeVariable : typeVariables) {
					if (CharOperation.equals(parameterType.toCharArray(), typeVariable))
						return false;
				}
			}
		}

		return true;
	}

	/// adapted from org.eclipse.jdt.internal.codeassist.InternalExtendedCompletionContext
	public boolean canUseDiamond(String[] parameterTypes, char[] fullyQualifiedTypeName) {
		ITypeBinding guessedType = null;
		// If no LHS or return type expected, then we can safely use diamond
		char[][] expectedTypekeys= this.getExpectedTypesKeys();
		if (expectedTypekeys == null || expectedTypekeys.length == 0)
			return true;

		// Next, find out whether any of the constructor parameters are the same as one of the
		// class type variables. If yes, diamond cannot be used.
		Optional<IBinding> potentialMatch = this.bindingsAcquirer.get() //
				.filter(binding -> {
					for (char[] expectedTypekey : expectedTypekeys) {
						if (CharOperation.equals(expectedTypekey, binding.getKey().toCharArray())) {
							return true;
						}
					}
					return false;
				}) //
				.findFirst();
		if (potentialMatch.isPresent() && potentialMatch.get() instanceof ITypeBinding match) {
			guessedType = match;
		}
		if (guessedType != null && !guessedType.isRecovered()) {
			// the erasure must be used because guessedType can be a RawTypeBinding
			guessedType = guessedType.getErasure();
			ITypeBinding[] typeVars = guessedType.getTypeParameters();
			for (String parameterType : parameterTypes) {
				for (ITypeBinding typeVar : typeVars) {
					if (CharOperation.equals(parameterType.toCharArray(), typeVar.getName().toCharArray())) {
						return false;
					}
				}
			}
			return true;
		}
		return false;
	}



	private static boolean castCompatable(ITypeBinding typeBinding, String sig2) {
		String sig1 = typeBinding.getKey().replace('/', '.');
		// NOTE: this is actually the "raw" version (no type arguments, no type params)
		String sig1Raw = new String(Signature.getTypeErasure(sig1.toCharArray()));
		// TODO: consider autoboxing numbers; upstream JDT doesn't handle this yet but it would be nice
		switch (sig1) {
			case Signature.SIG_LONG:
				return sig2.equals(Signature.SIG_LONG)
						|| sig2.equals(Signature.SIG_DOUBLE)
						|| sig2.equals(Signature.SIG_FLOAT);
			case Signature.SIG_INT:
				return sig2.equals(Signature.SIG_LONG)
						|| sig2.equals(Signature.SIG_INT)
						|| sig2.equals(Signature.SIG_DOUBLE)
						|| sig2.equals(Signature.SIG_FLOAT);
			case Signature.SIG_BYTE:
				return sig2.equals(Signature.SIG_LONG)
						|| sig2.equals(Signature.SIG_INT)
						|| sig2.equals(Signature.SIG_BYTE)
						|| sig2.equals(Signature.SIG_DOUBLE)
						|| sig2.equals(Signature.SIG_FLOAT);
			case Signature.SIG_DOUBLE:
			case Signature.SIG_FLOAT:
				return sig2.equals(Signature.SIG_DOUBLE)
						|| sig2.equals(Signature.SIG_FLOAT);
		}
		if (sig1.equals(sig2) || sig1Raw.equals(sig2)) {
			return true;
		}
		if (typeBinding.getSuperclass() != null && castCompatable(typeBinding.getSuperclass(), sig2)) {
			return true;
		}
		for (ITypeBinding superInterface : typeBinding.getInterfaces()) {
			if (castCompatable(superInterface, sig2)) {
				return true;
			}
		}
		return false;
	}
}