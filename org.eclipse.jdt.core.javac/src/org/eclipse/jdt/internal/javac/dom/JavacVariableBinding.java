/*******************************************************************************
 * Copyright (c) 2023, Red Hat, Inc. and others.
 *
 * This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License 2.0
 * which accompanies this distribution, and is available at
 * https://www.eclipse.org/legal/epl-2.0/
 *
 * SPDX-License-Identifier: EPL-2.0
 *******************************************************************************/
package org.eclipse.jdt.internal.javac.dom;

import java.util.Objects;

import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.dom.IAnnotationBinding;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.JavacBindingResolver;

import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Symbol.ClassSymbol;
import com.sun.tools.javac.code.Symbol.MethodSymbol;
import com.sun.tools.javac.code.Symbol.TypeSymbol;
import com.sun.tools.javac.code.Symbol.VarSymbol;

public class JavacVariableBinding implements IVariableBinding {

	public final VarSymbol variableSymbol;
	private final JavacBindingResolver resolver;

	public JavacVariableBinding(VarSymbol sym, JavacBindingResolver resolver) {
		this.variableSymbol = sym;
		this.resolver = resolver;
	}

	@Override
	public IAnnotationBinding[] getAnnotations() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("Unimplemented method 'getAnnotations'");
	}

	@Override
	public int getKind() {
		return VARIABLE;
	}

	@Override
	public int getModifiers() {
		return JavacMethodBinding.toInt(this.variableSymbol.getModifiers());
	}

	@Override
	public boolean isDeprecated() {
		return this.variableSymbol.isDeprecated();
	}

	@Override
	public boolean isRecovered() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("Unimplemented method 'isRecovered'");
	}

	@Override
	public boolean isSynthetic() {
		return (this.variableSymbol.flags() & Flags.SYNTHETIC) != 0;
	}

	@Override
	public IField getJavaElement() {
		if (this.variableSymbol.owner instanceof TypeSymbol parentType) {//field
			return new JavacTypeBinding(parentType, this.resolver).getJavaElement().getField(this.variableSymbol.name.toString());
		}
		return null;
	}

	@Override
	public String getKey() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("Unimplemented method 'getKey'");
	}

	@Override
	public boolean isEqualTo(IBinding binding) {
		return binding instanceof JavacVariableBinding other && //
			Objects.equals(this.variableSymbol, other.variableSymbol) && //
			Objects.equals(this.resolver, other.resolver);
	}

	@Override
	public boolean isField() {
		return this.variableSymbol.owner instanceof ClassSymbol;
	}

	@Override
	public boolean isEnumConstant() {
		return this.variableSymbol.isEnum();
	}

	@Override
	public boolean isParameter() {
		return this.variableSymbol.owner instanceof MethodSymbol;
	}

	@Override
	public String getName() {
		return this.variableSymbol.getSimpleName().toString();
	}

	@Override
	public ITypeBinding getDeclaringClass() {
		Symbol parentSymbol = this.variableSymbol.owner;
		do {
			if (parentSymbol instanceof ClassSymbol clazz) {
				return new JavacTypeBinding(clazz, this.resolver);
			}
			parentSymbol = parentSymbol.owner;
		} while (parentSymbol != null);
		return null;
	}

	@Override
	public ITypeBinding getType() {
		return new JavacTypeBinding(this.variableSymbol.type, this.resolver);
	}

	@Override
	public int getVariableId() {
		return variableSymbol.adr; // ?
	}

	@Override
	public Object getConstantValue() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("Unimplemented method 'getConstantValue'");
	}

	@Override
	public IMethodBinding getDeclaringMethod() {
		Symbol parentSymbol = this.variableSymbol.owner;
		do {
			if (parentSymbol instanceof MethodSymbol method) {
				return new JavacMethodBinding(method, this.resolver);
			}
			parentSymbol = parentSymbol.owner;
		} while (parentSymbol != null);
		return null;
	}

	@Override
	public IVariableBinding getVariableDeclaration() {
		return this;
	}

	@Override
	public boolean isEffectivelyFinal() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("Unimplemented method 'isEffectivelyFinal'");
	}

}