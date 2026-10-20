/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ZMod
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Small-étale pullback admits left Kan extensions of abelian presheaves. -/
instance instHasLeftKanExtension_smallEtalePullback_addCommGrp
    {S T : Scheme.{u}} (f : T ⟶ S) (G : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (smallEtalePullback f).op.HasLeftKanExtension G := sorry

/-- Small-étale pullback admits left Kan extensions of `ZMod n`-module presheaves. -/
instance instHasLeftKanExtension_smallEtalePullback_zmod
    {n : ℕ} {S T : Scheme.{u}} (f : T ⟶ S)
    (G : S.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod n)) :
    (smallEtalePullback f).op.HasLeftKanExtension G := sorry

/-- Forgetting `ZMod n`-modules to abelian groups preserves left Kan extensions along
small-étale pullback. -/
instance instPreservesLeftKanExtensions_forget₂_zmod_smallEtalePullback
    {n : ℕ} {S T : Scheme.{u}} (f : T ⟶ S) :
    (forget₂ (ModuleCat.{u} (ZMod n)) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (smallEtalePullback f).op :=
  fun _ ↦ { preserves := by sorry }

/-- Small-étale topologies preserve sheafification of the forgetful functor from
`ZMod n`-modules to abelian groups. -/
instance instPreservesSheafification_forget₂_zmod_smallEtale
    {n : ℕ} {S : Scheme.{u}} :
    S.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} (ZMod n)) AddCommGrpCat.{u}) := sorry

/-- Inverse image of a small-étale sheaf of `ZMod (ℓ ^ n)`-modules commutes with forgetting
to abelian sheaves. -/
def zmodSheafPullback_compSheafComposeIso {ℓ n : ℕ} {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})] :
    (sheafCompose T.smallEtaleTopology
        (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})).obj
      ((zmodSheafPullback f (ℓ ^ n)).obj G) ≅
      ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).obj
        ((sheafCompose S.smallEtaleTopology
            (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})).obj G) :=
  (Functor.sheafPullback.compSheafComposeIso
      (smallEtalePullback f)
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})
      S.smallEtaleTopology T.smallEtaleTopology).app G

/-- The forgetful comparison identifies module inverse image with abelian inverse image. -/
theorem zmodSheafPullback_compSheafComposeIso_spec {ℓ n : ℕ} {S T : Scheme.{u}}
    (f : T ⟶ S)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    [HasSheafify S.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})] :
    zmodSheafPullback_compSheafComposeIso f G =
      (Functor.sheafPullback.compSheafComposeIso
          (smallEtalePullback f)
          (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})
          S.smallEtaleTopology T.smallEtaleTopology).app G := rfl

end AlgebraicGeometry.Scheme.Etale
