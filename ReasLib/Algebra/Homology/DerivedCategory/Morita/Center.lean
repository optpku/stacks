/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Algebra.Center
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Centers under Derived Morita Equivalence

An `R`-linear triangulated equivalence between the derived categories of right modules over
two `R`-algebras preserves their centers.  The commutative specialization then recovers the
algebras themselves.
-/

@[expose] public section

noncomputable section

universe uR uA uB

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped ModuleCat.Algebra

namespace DerivedCategory.Morita

variable {R : Type uR} [CommRing R]

/-- Remark 22.37.9 (09SD) (1): an `R`-linear triangulated equivalence between the derived
categories of right modules over `A` and `B` induces an `R`-algebra equivalence between their
centers. -/
@[stacks 09SD "derived invariance of centers"]
theorem nonempty_centerAlgEquiv
    {A : Type uA} {B : Type uB} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (e : RLinear.TriangulatedEquivalence R
      (DerivedCategory (ModuleCat Aᵐᵒᵖ)) (DerivedCategory (ModuleCat Bᵐᵒᵖ))) :
    Nonempty (Subalgebra.center R A ≃ₐ[R] Subalgebra.center R B) := sorry

/-- Remark 22.37.9 (09SD) (2): derived-equivalent commutative `R`-algebras are equivalent as
`R`-algebras. -/
@[stacks 09SD "commutative derived-equivalent algebras"]
theorem nonempty_algEquiv
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : RLinear.TriangulatedEquivalence R
      (DerivedCategory (ModuleCat Aᵐᵒᵖ)) (DerivedCategory (ModuleCat Bᵐᵒᵖ))) :
    Nonempty (A ≃ₐ[R] B) := sorry

end DerivedCategory.Morita
