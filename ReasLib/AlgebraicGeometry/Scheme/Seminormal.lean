/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty
public import ReasLib.AlgebraicGeometry.Scheme.Reduced
public import ReasLib.RingTheory.Seminormal

/-!
# Seminormal and Absolutely Weakly Normal Schemes

This leaf specializes the generic affine-local ring-property owner to the
standard seminormal and absolutely weakly normal ring conditions.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme is seminormal when its coordinate ring is seminormal on an
affine neighbourhood of every point. -/
abbrev Seminormal (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ SeminormalRing A)

/-- At every point of a seminormal scheme, there is an affine open
neighbourhood with seminormal coordinate ring. -/
theorem exists_affineOpen_seminormalRing (X : Scheme.{u}) [Seminormal X] (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ SeminormalRing (Γ(X, (U : X.Opens))) := sorry

/-- Unfold seminormality into the affine-open neighbourhood criterion. -/
theorem seminormal_iff (X : Scheme.{u}) :
    Seminormal X ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        SeminormalRing (Γ(X, (U : X.Opens))) := sorry

/-- Every seminormal scheme is reduced. -/
@[instance]
theorem isReduced_of_seminormal (X : Scheme.{u}) [Seminormal X] :
    IsReduced X := by
  refine (isReduced_iff_hasRingPropertyLocally X).2 ?_
  refine ⟨?_⟩
  intro x
  rcases exists_affineOpen_seminormalRing X x with ⟨U, hxU, hU⟩
  exact ⟨U, hxU, @isReduced_of_seminormalRing (Γ(X, (U : X.Opens))) _ hU⟩

/-- A scheme is absolutely weakly normal when its coordinate ring is
absolutely weakly normal on an affine neighbourhood of every point. -/
abbrev AbsolutelyWeaklyNormal (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A)

/-- At every point of an absolutely weakly normal scheme, there is an affine
open neighbourhood with absolutely weakly normal coordinate ring. -/
theorem exists_affineOpen_absolutelyWeaklyNormalRing (X : Scheme.{u})
    [AbsolutelyWeaklyNormal X] (x : X) :
    ∃ U : X.affineOpens,
      x ∈ (U : X.Opens) ∧ AbsolutelyWeaklyNormalRing (Γ(X, (U : X.Opens))) := sorry

/-- Absolutely weakly normal schemes are seminormal. -/
instance instSeminormalOfAbsolutelyWeaklyNormal (X : Scheme.{u}) [AbsolutelyWeaklyNormal X] :
    Seminormal X := sorry

/-- Unfold absolute weak normality into the affine-open neighbourhood
criterion. -/
theorem absolutelyWeaklyNormal_iff (X : Scheme.{u}) :
    AbsolutelyWeaklyNormal X ↔
      ∀ x : X,
        ∃ U : X.affineOpens,
          x ∈ (U : X.Opens) ∧ AbsolutelyWeaklyNormalRing (Γ(X, (U : X.Opens))) := sorry

/-- Every absolutely weakly normal scheme is reduced. -/
theorem isReduced_of_absolutelyWeaklyNormal (X : Scheme.{u}) [AbsolutelyWeaklyNormal X] :
    IsReduced X :=
  @isReduced_of_seminormal X (instSeminormalOfAbsolutelyWeaklyNormal X)

end AlgebraicGeometry.Scheme
