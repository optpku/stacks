/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleComparison

/-!
# Cohomology of étale-to-pro-étale inverse images

On an affine scheme, inverse images of injective abelian étale sheaves have
vanishing pro-étale cohomology in positive degrees.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- On an affine scheme, the inverse image of an injective abelian sheaf on the
small étale site has zero pro-étale cohomology in every positive degree. -/
theorem etaleToProEtPullback_injective_isZero_cohomology
    (X : Scheme.{u}) [IsAffine X]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}, (etaleToProEt X).op.HasLeftKanExtension F]
    [HasSheafify (ProEt.topology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (ProEt.topology X) AddCommGrpCat.{u})]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
    {p : ℕ} (hp : 0 < p) :
    IsZero (((etaleToProEtPullback X AddCommGrpCat.{u}).obj I).H' p (ProEt.mk (𝟙 X))) :=
  sorry

end AlgebraicGeometry.Scheme
