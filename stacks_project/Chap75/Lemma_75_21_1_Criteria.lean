/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap75.Lemma_75_21_1_Pullback
public import stacks_project.Chap75.«75_21_0_1_Comparison»

/-!
# Étale cohomology base-change criteria on algebraic spaces

For a cartesian square of algebraic spaces, pointwise invertibility of the geometric-point
maps 75.21.0.1 is equivalent to the scheme-level criteria of Lemma 36.26.1 on every étale
scheme chart, and on some étale scheme chart with surjective `U' → X'`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- Condition (1) of Lemma 75.21.1: the geometric-point cohomology maps 75.21.0.1 are
isomorphisms. -/
def cohomologyBaseChangeHolds {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    Prop :=
  ∀ (xbar' : GeometricPoint X') (i : ℤ),
    IsIso (pointCohomologyMap g' f' f g sq.w K K' α xbar' i)

/-- `cohomologyBaseChangeHolds` is pointwise invertibility of `pointCohomologyMap`. -/
theorem cohomologyBaseChangeHolds_iff {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    cohomologyBaseChangeHolds sq K K' α ↔
      ∀ (xbar' : GeometricPoint X') (i : ℤ),
        IsIso (pointCohomologyMap g' f' f g sq.w K K' α xbar' i) :=
  sorry

/-- Pointwise invertibility of the geometric-point maps is equivalent to Lemma 36.26.1 on
every étale scheme chart. -/
theorem cohomologyBaseChange_pointwise_iff_etale (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) (K : DerivedQCoh X)
    (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    cohomologyBaseChangeHolds sq K K' α ↔
      ∀ c : EtaleBaseChangeChart g' f' f g, c.schemeHolds sq K K' α :=
  sorry

/-- Pointwise invertibility of the geometric-point maps is equivalent to Lemma 36.26.1 on
some étale scheme chart with `U' → X'` surjective. -/
theorem cohomologyBaseChange_pointwise_iff_etaleCover (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) (K : DerivedQCoh X)
    (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    cohomologyBaseChangeHolds sq K K' α ↔
      ∃ c : EtaleBaseChangeChart g' f' f g,
        Surjective (c.toX' sq) ∧ c.schemeHolds sq K K' α :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
