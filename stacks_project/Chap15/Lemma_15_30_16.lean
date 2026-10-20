/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.MvPolynomial.LinearForm

/-!
# Regularity of a multivariable linear form

@stack 068P
-/

@[expose] public section

/- Lemma 15.30.16, tag `068P`: injectivity of `x ↦ (x * a i)ᵢ` implies that the
multivariable linear form `∑ i, C (a i) * X i` is regular. -/
@[stacks 068P "Lemma 15.30.16"]
#check @MvPolynomial.isRegular_linearForm_of_smulFamilyMap_injective

/- The equivalent principal-open localization-family formulation. -/
#check @MvPolynomial.isRegular_linearForm_of_awayFamilyMap_injective
