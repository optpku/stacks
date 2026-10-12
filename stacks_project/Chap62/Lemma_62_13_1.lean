/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Lemma_62_13_1_Comp

/-!
# Bilinearity of composition of families of cycles on fibres

This file records that the construction `α ∘ β` of Section 62.13 is additive
in each family.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- Lemma 62.13.1 (1): the construction `α ∘ β` is additive in the family of
`r`-cycles on fibres of `X / Y`, i.e. `(α₁ + α₂) ∘ β = α₁ ∘ β + α₂ ∘ β`. -/
@[stacks 0H6I]
theorem comp_add_left {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℤ}
    (α₁ α₂ : CyclesOnFibers f r) (β : CyclesOnFibers p e) :
    comp (α₁ + α₂) β = comp α₁ β + comp α₂ β := sorry

/-- Lemma 62.13.1 (2): the construction `α ∘ β` is additive in the family of
`e`-cycles on fibres of `Y / S`, i.e. `α ∘ (β₁ + β₂) = α ∘ β₁ + α ∘ β₂`. -/
@[stacks 0H6I]
theorem comp_add_right {S X Y : Scheme.{u}} (p : Y ⟶ S) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType f] {r e : ℤ}
    (α : CyclesOnFibers f r) (β₁ β₂ : CyclesOnFibers p e) :
    comp α (β₁ + β₂) = comp α β₁ + comp α β₂ := sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
