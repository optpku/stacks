module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize
public import stacks_project.Chap99.Remark_99_5_5_BaseChange
public import stacks_project.Chap99.Remark_99_5_5_Forget

/-!
# Remark 99.5.5

In Situation 99.5.1 the rule `(T, g, F) ↦ (T, g)` is a 1-morphism of stacks in
groupoids `Coh_{X/B} ⟶ 𝒮_B`. For `g : B' ⟶ B`, the square comparing
`Coh_{X'/B'}` with `Coh_{X/B}` over `Sch/B' → Sch/B` (equivalently `𝒮_{B'} → 𝒮_B`)
is a 2-fibre product square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open CategoryTheory.Limits CategoricalPullback

noncomputable section

universe u

/- Remark 99.5.5 (1): in Situation 99.5.1 the rule `(T, g, F) ↦ (T, g)` defines a
1-morphism `Coh_{X/B} ⟶ 𝒮_B` of stacks in groupoids. -/
@[stacks 08LP] #check toBase

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}

/-- The commutative square with apex `Coh_{X'/B'}`, projecting to `Coh_{X/B}` and to
`Sch/B'`, over `Sch/B`. Here `Sch/B` is the source's other notation for `𝒮_B`. -/
def square (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f] :
    CatCommSqOver (toSchemesOver f) (CostructuredArrow.map g) (Obj (pullback.snd f g)) where
  fst := baseChange f g
  snd := toSchemesOver (pullback.snd f g)
  iso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} _ ↦ rfl)

/-- The comparison from `Coh_{X'/B'}` to the explicit categorical pullback of
`toSchemesOver f` and `CostructuredArrow.map g`. -/
abbrev square.comparison (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f] :=
  (square f g).comparison

/-- Remark 99.5.5 (2): for a morphism `g : B' ⟶ B` of algebraic spaces over `S`,
setting `X' = X ×_B B'` and `f' = pullback.snd f g`, the square
`Coh_{X'/B'} → Coh_{X/B}` over `Sch/B' → Sch/B` (equivalently `𝒮_{B'} → 𝒮_B`)
is a 2-fibre product square. -/
@[stacks 08LP, instance]
instance square.instIsBilimit (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f] :
    CatCommSqOver.Resized.IsBilimit (square f g) :=
  sorry

/-- The comparison functor is an equivalence when the square is a 2-fibre product. -/
instance square.comparison_isEquivalence (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    [CatCommSqOver.Resized.IsBilimit (square f g)] :
    (square.comparison f g).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
