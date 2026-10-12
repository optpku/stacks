/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived limits of degreewise single objects

The Milnor sequence for a tower concentrated in degree `q` has possible cohomology only in
degrees `q` and `q + 1`.  This leaf records the upper vanishing and identifies the latter object
with the first derived inverse limit of the underlying tower.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory.IsDerivedLimit

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable [HasCountableProducts C] [HasExactLimitsOfShape (Discrete ℕ) C]
variable [HasLimitsOfShape ℕᵒᵖ C]

/-- A derived limit of a tower concentrated in degree `q` has zero cohomology strictly above
`q + 1`. -/
@[stacks 0947 "derived limit of single objects: upper vanishing"]
theorem single_homology_isZero_of_gt
    (F : SequentialInverseSystem C) (K : DerivedCategory C)
    (q p : ℤ)
    (hK : IsDerivedLimit
      (F ⋙ DerivedCategory.singleFunctor C q) K)
    (hp : q + 1 < p) :
    IsZero ((DerivedCategory.homologyFunctor C p).obj K) := sorry

/-- The cohomology in degree `q + 1` of a derived limit of degree-`q` single objects is the
first derived inverse limit of the underlying tower. -/
@[stacks 0947 "derived limit of single objects: first derived limit"]
theorem single_homology_succ_isomorphic_firstDerivedLimit
    (F : SequentialInverseSystem C) (K : DerivedCategory C)
    (q : ℤ)
    (hK : IsDerivedLimit
      (F ⋙ DerivedCategory.singleFunctor C q) K) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor C (q + 1)).obj K)
      F.firstDerivedLimit := sorry

end CategoryTheory.IsDerivedLimit

end
