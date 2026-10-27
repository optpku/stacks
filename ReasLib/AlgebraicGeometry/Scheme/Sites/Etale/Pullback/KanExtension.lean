/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback.CommaFinallySmall
public import ReasLib.CategoryTheory.Functor.KanExtension.FinallySmall

/-! # Pointwise left Kan data for small étale pullback

For arbitrary morphisms of schemes and arbitrary presheaves with coefficients
admitting universe-u colimits. The full comma is finally small by the bounded
chart and gluing construction. Stacks' inverse-image colimit formula provides
context; 04D3 concerns representable sheaves and is not the literal statement.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

universe u uA vA

namespace AlgebraicGeometry.Scheme.Etale

/-- Final-smallness of the full comma indexing étale inverse-image presheaves. -/
noncomputable def smallEtalePullbackFinallySmall {S T : Scheme.{u}} (f : T ⟶ S) :
    ∀ V : T.Etaleᵒᵖ,
      FinallySmall.{u} (CostructuredArrow (Scheme.smallEtalePullback f).op V) := by
  intro V
  simpa [PullbackBounds.CommaFinallySmall.Comma] using
    (PullbackBounds.CommaFinallySmall.finallySmall f V.unop)

/-- Actual pointwise extension and unit, bundled in Mathlib's native `LeftExtension`. -/
noncomputable def smallEtaleLeftExtension
    {S T : Scheme.{u}} (f : T ⟶ S)
    {A : Type uA} [Category.{vA} A] [HasColimitsOfSize.{u, u} A]
    (G : S.Etaleᵒᵖ ⥤ A) : (Scheme.smallEtalePullback f).op.LeftExtension G :=
  Functor.pointwiseLeftExtensionOfFinallySmall
    (Scheme.smallEtalePullback f).op G (smallEtalePullbackFinallySmall f)

/-- Universal property of the displayed functor and unit. -/
theorem smallEtaleLeftExtension_isLeftKanExtension
    {S T : Scheme.{u}} (f : T ⟶ S)
    {A : Type uA} [Category.{vA} A] [HasColimitsOfSize.{u, u} A]
    (G : S.Etaleᵒᵖ ⥤ A) :
    (smallEtaleLeftExtension f G).right.IsLeftKanExtension
      (smallEtaleLeftExtension f G).hom :=
  Functor.pointwiseLeftExtensionOfFinallySmall_isLeftKanExtension
    (Scheme.smallEtalePullback f).op G (smallEtalePullbackFinallySmall f)

/-- The existence certificate comes from the displayed genuine extension and unit. -/
theorem smallEtaleHasLeftKanExtension
    {S T : Scheme.{u}} (f : T ⟶ S)
    {A : Type uA} [Category.{vA} A] [HasColimitsOfSize.{u, u} A]
    (G : S.Etaleᵒᵖ ⥤ A) : (Scheme.smallEtalePullback f).op.HasLeftKanExtension G := by
  let E := smallEtaleLeftExtension f G
  letI : E.right.IsLeftKanExtension E.hom :=
    smallEtaleLeftExtension_isLeftKanExtension f G
  exact Functor.HasLeftKanExtension.mk E.right E.hom

end AlgebraicGeometry.Scheme.Etale
