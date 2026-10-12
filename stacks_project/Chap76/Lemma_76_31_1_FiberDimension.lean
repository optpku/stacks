/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_34_3_FiberDimension
public import stacks_project.Chap68.Lemma_68_18_6_Fibre
public import stacks_project.Chap68.Lemma_68_18_10_Fibre

/-!
# Target-indexed fibre dimensions of morphisms of algebraic spaces

The fibre dimension of a morphism of algebraic spaces at a point of the
target is the supremum of the source-indexed relative dimensions along the
set-theoretic fibre. It is `⊥` off the image of the map on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre dimension of a morphism `f : X ⟶ Y` of algebraic spaces at a
point of `Y`, as the supremum of the relative dimensions of `f` at points of
the set-theoretic fibre. -/
noncomputable def fiberDimension {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Points Y → WithBot ℕ∞ :=
  fun y ↦ ⨆ x ∈ fiberOver f y, fiberDimensionAt f x

/-- Evaluating `fiberDimension f` at a point of `Y` is the supremum of
`fiberDimensionAt f` over the set-theoretic fibre. -/
theorem fiberDimension_apply {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) :
    fiberDimension f y = ⨆ x ∈ fiberOver f y, fiberDimensionAt f x :=
  sorry

/-- The fibre dimension of `f` at `y` is `⊥` if and only if `y` is not in the
image of `Points.map f`. -/
theorem fiberDimension_eq_bot_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] (y : Points Y) :
    fiberDimension f y = ⊥ ↔ y ∉ Set.range (Points.map f) :=
  sorry

/-- The fibre dimension of `f` at `y` is at most `d` if and only if `f` has
relative dimension at most `d` at every point of `X` mapping to `y`. -/
theorem fiberDimension_le_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) (d : ℕ) :
    fiberDimension f y ≤ (d : WithBot ℕ∞) ↔
      ∀ x ∈ fiberOver f y, RelativeDimensionLEAt f d x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
