module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize
public import stacks_project.Chap108.Lemma_108_12_1_Map
public import stacks_project.Chap99.Remark_99_16_7_BaseChange

/-!
# Remark 99.16.7

In Situation 99.16.3 the rule `(T, g, E) ↦ (T, g)` is a 1-morphism of stacks in
groupoids `Complexes_{X/B} ⟶ 𝒮_B`. For `g : B' ⟶ B`, the square comparing
`Complexes_{X'/B'}` with `Complexes_{X/B}` over `Sch/B' → Sch/B` (equivalently
`𝒮_{B'} → 𝒮_B`) is a 2-fibre product square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Complexes
open CategoryTheory.Limits CategoricalPullback

noncomputable section

universe u

/- Remark 99.16.7 (1): in Situation 99.16.3 the rule `(T, g, E) ↦ (T, g)` defines a
1-morphism `Complexes_{X/B} ⟶ 𝒮_B` of stacks in groupoids. -/
@[stacks 0DLI] #check toBase

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}

/-- The commutative square with apex `Complexes_{X'/B'}`, projecting to
`Complexes_{X/B}` and to `Sch/B'`, over `Sch/B`. Here `Sch/B` is the source's
other notation for `𝒮_B`. -/
def square (f : X ⟶ B) (g : B' ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    CatCommSqOver (toSchemesOver f) (CostructuredArrow.map g) (Obj (pullback.snd f g)) where
  fst := baseChange f g
  snd := toSchemesOver (pullback.snd f g)
  iso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} _ ↦ rfl)

/-- The comparison from `Complexes_{X'/B'}` to the explicit categorical pullback of
`toSchemesOver f` and `CostructuredArrow.map g`. -/
abbrev square.comparison (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] :=
  (square f g).comparison

/-- Remark 99.16.7 (2): for a morphism `g : B' ⟶ B` of algebraic spaces over `S`,
setting `X' = X ×_B B'` and `f' = pullback.snd f g`, the square
`Complexes_{X'/B'} → Complexes_{X/B}` over `Sch/B' → Sch/B` (equivalently
`𝒮_{B'} → 𝒮_B`) is a 2-fibre product square. -/
@[stacks 0DLI, instance]
instance square.instIsBilimit (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] :
    CatCommSqOver.Resized.IsBilimit (square f g) :=
  sorry

/-- The comparison functor is an equivalence when the square is a 2-fibre product. -/
instance square.comparison_isEquivalence (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    [CatCommSqOver.Resized.IsBilimit (square f g)] :
    (square.comparison f g).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
