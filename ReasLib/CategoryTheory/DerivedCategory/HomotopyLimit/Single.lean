/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.HomotopyLimit.Cohomology
public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived limits of single-degree towers

This file is the presentation-independent interface for a sequential homotopy limit of objects
concentrated in one degree.  The output uses the canonical Milnor cokernel
`SequentialInverseSystem.Milnor.ProductCone.canonicalR1`; the older
`IsDerivedLimit`/`firstDerivedLimit` spelling is retained in the compatibility leaf.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory.HomotopyLimit.IsOf

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [HasCountableProducts C] [HasExactLimitsOfShape (Discrete ℕ) C]
variable [HasLimitsOfShape ℕᵒᵖ C]

/-- A homotopy limit of a tower concentrated in degree `q` has zero cohomology strictly above
`q + 1`. -/
@[stacks 0947 "derived limit of single objects: upper vanishing"]
theorem single_homology_isZero_of_gt
    (F : SequentialInverseSystem C) (K : DerivedCategory C)
    (q p : ℤ)
    (hK : HomotopyLimit.IsOf
      (F ⋙ DerivedCategory.singleFunctor C q) K)
    (hp : q + 1 < p) :
    IsZero ((DerivedCategory.homologyFunctor C p).obj K) := sorry

/-- The cohomology in degree `q + 1` of a homotopy limit of degree-`q` single objects is the
canonical first derived inverse limit of the underlying tower. -/
@[stacks 0947 "derived limit of single objects: first derived limit"]
theorem single_homology_succ_isomorphic_canonicalR1
    (F : SequentialInverseSystem C) (K : DerivedCategory C)
    (q : ℤ)
    (hK : HomotopyLimit.IsOf
      (F ⋙ DerivedCategory.singleFunctor C q) K) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor C (q + 1)).obj K)
      (SequentialInverseSystem.Milnor.ProductCone.canonicalR1 F) := sorry

end CategoryTheory.HomotopyLimit.IsOf

end
