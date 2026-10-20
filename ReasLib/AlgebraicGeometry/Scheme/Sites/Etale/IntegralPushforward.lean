/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyA
public import ReasLib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u w

namespace AlgebraicGeometry

namespace Scheme.SmallEtaleDirectImage

/-- The small étale direct image preserves locally surjective morphisms for an integral
morphism of schemes. -/
instance preservesLocallySurjective_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology (Type (u + 1))]
    [IsIntegralHom f] :
    (Scheme.smallEtaleDirectImage f).PreservesLocallySurjective := sorry

end Scheme.SmallEtaleDirectImage

namespace SmallAbelianPushforward

/-- The additive small étale direct image preserves epimorphisms for an integral morphism
of schemes. -/
instance preservesEpimorphisms_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    [IsIntegralHom f] :
    (smallAbelianPushforward f).PreservesEpimorphisms := sorry

/-- The additive small étale direct image is exact for an integral morphism of schemes. -/
theorem exact_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    [IsIntegralHom f] :
    exactFunctor _ _ (smallAbelianPushforward f) := sorry

end SmallAbelianPushforward

end AlgebraicGeometry
