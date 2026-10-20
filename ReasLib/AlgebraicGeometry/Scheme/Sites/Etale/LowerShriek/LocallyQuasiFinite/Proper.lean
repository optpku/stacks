/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.ForgetAbelian
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Proper

/-!
# Lower shriek and proper pushforward in a commutative triangle
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Forgetting coefficients intertwines compact-support direct image with
compact-support direct image of abelian sheaves. -/
def lowerShriekModule_forgetAbelianIso {S T : Scheme.{u}} (h : S ⟶ T)
    [LocallyQuasiFinite h] (Λ : Type u) [Ring Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [T.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})] :
    lowerShriekModule h Λ ⋙
        sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
      sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        lowerShriek h :=
  asIso (lowerShriekModule_forgetNatTrans h Λ)

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [IsProper h]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]

-- Module visibility: allow this private construction in the public comparison.
set_option backward.privateInPublic true in
/-- The abelian sheaf identification `(f ≫ h)_! ≅ h_* ∘ f_!` obtained by mixed
composition of compact support followed by the proper identification
`h_! ≅ h_*`. -/
private def lowerShriek_compProperIso_ofComp
    [lqf_comp : LocallyQuasiFinite (f ≫ h)]
    [lft_comp : LocallyOfFiniteType (f ≫ h)] :
    lowerShriek (f ≫ h) ≅ lowerShriek f ⋙ etaleAbelianPushforward h :=
  lowerShriekCompIso f h ≪≫
    isoWhiskerLeft (lowerShriek f) (etaleLowerShriekIso h)

variable {g : X ⟶ Z} (w : f ≫ h = g)
variable [hg : LocallyQuasiFinite g] [hgt : LocallyOfFiniteType g]

-- Module visibility: retain the concrete construction as a private implementation detail.
set_option backward.privateInPublic true in
/-- The abelian sheaf isomorphism `g_! ≅ h_* ∘ f_!` obtained by transporting
along `f ≫ h = g`, composing compact support, and identifying proper
`h_!` with `h_*`. -/
def lowerShriek_compProperIso :
    lowerShriek g ≅ lowerShriek f ⋙ etaleAbelianPushforward h :=
  w ▸ lowerShriek_compProperIso_ofComp f h
    (lqf_comp := w.symm ▸ hg) (lft_comp := w.symm ▸ hgt)

-- Module visibility: retain the concrete construction as a private implementation detail.
set_option backward.privateInPublic true in
/-- The forward map of `lowerShriek_compProperIso` is transport along the
triangle, mixed composition, and the proper identification `h_! ≅ h_*`. -/
theorem lowerShriek_compProperIso_hom :
    (lowerShriek_compProperIso f h w).hom =
      (w ▸ (lowerShriek_compProperIso_ofComp f h
          (lqf_comp := w.symm ▸ hg) (lft_comp := w.symm ▸ hgt)).hom) := by
  cases w
  rfl

variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]

/-- Forgetting coefficients identifies `h_* (f_! F)` with
`(etaleAbelianPushforward h) ((lowerShriek f) (forget F))`. -/
def lowerShriekModule_compProperIso_forgetRight
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Z.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        (((smallEtalePullback h).sheafPushforwardContinuous
            (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).obj
          ((lowerShriekModule f Λ).obj F)) ≅
      (etaleAbelianPushforward h).obj
        ((lowerShriek f).obj
          ((sheafCompose X.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) :=
  (modulePushforward_forgetAbelianIso h Λ).app
      ((lowerShriekModule f Λ).obj F) ≪≫
    (etaleAbelianPushforward h).mapIso
      ((lowerShriekModule_forgetAbelianIso f Λ).app F)

/-- The forward proper-triangle map after forgetting scalars, with all three canonical legs. -/
def lowerShriekModule_compProperHomAb
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  ((lowerShriekModule_forgetAbelianIso g Λ).hom.app F ≫
        ((lowerShriek_compProperIso f h w).app
            ((sheafCompose X.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        (lowerShriekModule_compProperIso_forgetRight f h Λ F).inv)

/-- The reverse proper-triangle map after forgetting scalars. -/
def lowerShriekModule_compProperInvAb
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  ((lowerShriekModule_compProperIso_forgetRight f h Λ F).hom ≫
        ((lowerShriek_compProperIso f h w).app
            ((sheafCompose X.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).inv ≫
        (lowerShriekModule_forgetAbelianIso g Λ).inv.app F)

/-- The actual forward proper-support comparison commutes with coefficient scalars. -/
theorem lowerShriekModule_compProperHomAb_linear
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleModuleSheafHomLinear (lowerShriekModule_compProperHomAb f h w Λ F) := sorry

/-- The actual inverse proper-support comparison commutes with coefficient scalars. -/
theorem lowerShriekModule_compProperInvAb_linear
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleModuleSheafHomLinear (lowerShriekModule_compProperInvAb f h w Λ F) := sorry

/-- The lifted forward and reverse proper-triangle maps compose to the identity. -/
theorem lowerShriekModule_compProperIso_app_hom_inv_id
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    liftEtaleModuleSheafHom (lowerShriekModule_compProperHomAb f h w Λ F)
        (lowerShriekModule_compProperHomAb_linear f h w Λ F) ≫
      liftEtaleModuleSheafHom (lowerShriekModule_compProperInvAb f h w Λ F)
        (lowerShriekModule_compProperInvAb_linear f h w Λ F) = 𝟙 _ := sorry

/-- The lifted reverse and forward proper-triangle maps compose to the identity. -/
theorem lowerShriekModule_compProperIso_app_inv_hom_id
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    liftEtaleModuleSheafHom (lowerShriekModule_compProperInvAb f h w Λ F)
        (lowerShriekModule_compProperInvAb_linear f h w Λ F) ≫
      liftEtaleModuleSheafHom (lowerShriekModule_compProperHomAb f h w Λ F)
        (lowerShriekModule_compProperHomAb_linear f h w Λ F) = 𝟙 _ := sorry

/-- The module proper-triangle isomorphism has the scalar-linear section maps
of the abelian proper-triangle comparison. -/
def lowerShriekModule_compProperIso_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule g Λ).obj F ≅
      ((smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology).obj
          ((lowerShriekModule f Λ).obj F) where
  hom := liftEtaleModuleSheafHom (lowerShriekModule_compProperHomAb f h w Λ F)
    (lowerShriekModule_compProperHomAb_linear f h w Λ F)
  inv := liftEtaleModuleSheafHom (lowerShriekModule_compProperInvAb f h w Λ F)
    (lowerShriekModule_compProperInvAb_linear f h w Λ F)
  hom_inv_id := lowerShriekModule_compProperIso_app_hom_inv_id f h w Λ F
  inv_hom_id := lowerShriekModule_compProperIso_app_inv_hom_id f h w Λ F

/-- The sheaf-level module isomorphism `g_! ≅ h_* ∘ f_!`. -/
def lowerShriekModule_compProperIso :
    lowerShriekModule g Λ ≅
      lowerShriekModule f Λ ⋙
        (smallEtalePullback h).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology :=
  NatIso.ofComponents (lowerShriekModule_compProperIso_app f h w Λ) sorry

/-- The forward map of `lowerShriekModule_compProperIso` is assembled
componentwise from the abelian comparison after forgetting coefficients. -/
theorem lowerShriekModule_compProperIso_hom
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule_compProperIso f h w Λ).hom.app F =
      liftEtaleModuleSheafHom (lowerShriekModule_compProperHomAb f h w Λ F)
        (lowerShriekModule_compProperHomAb_linear f h w Λ F) := rfl


end AlgebraicGeometry.Scheme.Etale

end
