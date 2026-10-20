/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfect complexes over quotient rings

@stack 07LU
@stack 09AS

This leaf owns descent of perfectness across nilpotent quotient thickenings and the two-ideal
gluing criterion for derived quotient base changes.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

-- Local instance justification (search instability): quotient base changes are formed in the
-- standard t-structure on derived categories of modules.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

variable {R : Type u} [CommRing R]

/-- Lemma 15.79.4 (07LU): perfectness descends from the derived reduction modulo a nilpotent
ideal. -/
@[stacks 07LU "perfectness across a nilpotent quotient"]
theorem isPerfect_of_derivedTensorWithAlgebra_quotient_isPerfect_of_isNilpotent
    (I : Ideal R) (K : DerivedCategory (ModuleCat R))
    (hbase : (K ⊗[R]^L[(R ⧸ I)]).IsPerfect) (hI : IsNilpotent I) :
    K.IsPerfect := sorry

/-- Lemma 15.79.5 (09AS): if the derived reductions of `K` modulo `I` and modulo `J` are
perfect, then its derived reduction modulo `I * J` is perfect. -/
@[stacks 09AS "perfectness modulo a product of ideals"]
theorem isPerfect_derivedTensorWithAlgebra_quotient_mul_of_isPerfect_quotient_left_right
    (I J : Ideal R) (K : DerivedCategory (ModuleCat R))
    (hI : (K ⊗[R]^L[(R ⧸ I)]).IsPerfect)
    (hJ : (K ⊗[R]^L[(R ⧸ J)]).IsPerfect) :
    (K ⊗[R]^L[(R ⧸ (I * J))]).IsPerfect := sorry

end CategoryTheory
