/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.Polynomial
public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Quotient
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.115.4

@stack 00OY
-/

@[stacks 00OY "(1), finite injective quotient normalization"]
#check @MvPolynomial.NoetherNormalization.exists_finite_injective_quotient_normalization

@[stacks 00OY "(2), dimension of a finite injective normalization"]
#check @MvPolynomial.AlgHom.ringKrullDim_eq_of_injective_finite
