/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange

/-!
# Étale cohomology base-change criteria on algebraic spaces

For a cartesian square of algebraic spaces, pointwise invertibility of the geometric-point
cohomology maps is equivalent to the scheme-level base-change criterion on every étale
scheme chart, and on some étale scheme chart with surjective `U' → X'`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- The canonical geometric-point cohomology base-change maps are isomorphisms at every
geometric point and in every integer degree. -/
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
        IsIso (pointCohomologyMap g' f' f g sq.w K K' α xbar' i) := sorry

/-- Pointwise invertibility of the geometric-point cohomology base-change maps is equivalent
to the scheme base-change criterion on every compatible étale scheme chart. -/
theorem cohomologyBaseChange_pointwise_iff_etale (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) (K : DerivedQCoh X)
    (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    cohomologyBaseChangeHolds sq K K' α ↔
      ∀ c : EtaleBaseChangeChart g' f' f g, c.schemeHolds sq K K' α := sorry

/-- Pointwise invertibility of the geometric-point cohomology base-change maps is equivalent
to the scheme base-change criterion on some compatible étale scheme chart with surjective
induced map to the base-changed space. -/
theorem cohomologyBaseChange_pointwise_iff_etaleCover (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) (K : DerivedQCoh X)
    (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    cohomologyBaseChangeHolds sq K K' α ↔
      ∃ c : EtaleBaseChangeChart g' f' f g,
        Surjective (c.toX' sq) ∧ c.schemeHolds sq K K' α := sorry

/-- For a cartesian square of algebraic spaces, pointwise invertibility of the canonical
cohomology base-change maps is equivalent to the scheme criterion on every compatible
étale scheme chart and to that criterion on one chart surjecting onto the base-changed space. -/
theorem cohomologyBaseChange_tfae_etale {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K') :
    List.TFAE
      [ cohomologyBaseChangeHolds sq K K' α
      , ∀ c : EtaleBaseChangeChart g' f' f g, c.schemeHolds sq K K' α
      , ∃ c : EtaleBaseChangeChart g' f' f g,
          AlgebraicSpace.Surjective (c.toX' sq) ∧ c.schemeHolds sq K K' α ] := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
