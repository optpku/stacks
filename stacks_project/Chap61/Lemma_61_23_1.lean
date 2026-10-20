/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtalePushforward
import StacksCheckRecall

/-!
# Lemma 61.23.1

For a quasi-compact quasi-separated morphism of schemes, pushforward along
`f` commutes with `ε⁻¹` from the small étale site to the small pro-étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt

universe u

/- Lemma 61.23.1 (1): for every sheaf of sets, the canonical comparison between
étale pushforward followed by comparison inverse image and pro-étale pushforward
after comparison inverse image is an isomorphism. -/
@[stacks 09A6] #check (AlgebraicGeometry.Scheme.etaleToProEt_pushforwardHom_isIso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [∀ F : Y.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt Y).op.HasLeftKanExtension F]
    [∀ F : X.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt X).op.HasLeftKanExtension F]
    [∀ F : Y.Etaleᵒᵖ ⥤ Type (u + 1), (smallEtalePullback f).op.HasLeftKanExtension F]
    [∀ F : Y.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [HasWeakSheafify (topology X) (Type (u + 1))]
    [HasWeakSheafify (topology Y) (Type (u + 1))]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))),
    IsIso ((etaleToProEt_pushforwardHom (Type (u + 1)) f).app F))

/- Lemma 61.23.1 (2): for every abelian étale sheaf embedded in degree zero,
the corresponding canonical comparison of bounded-below derived pushforwards
is an isomorphism. -/
@[stacks 09A6] #check (AlgebraicGeometry.Scheme.etaleToProEt_derivedPushforwardHom_isIso :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology Y) AddCommGrpCat.{u + 1}]
    [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt Y).op.HasLeftKanExtension F]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt X).op.HasLeftKanExtension F]
    [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback f).op.HasLeftKanExtension F]
    [∀ F : Y.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (baseChange f).op.HasLeftKanExtension F]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
    IsIso (etaleToProEt_derivedPushforwardHom f F))
