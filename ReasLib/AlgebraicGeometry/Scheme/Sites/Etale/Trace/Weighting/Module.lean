/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.Weighting.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Forget
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f).op]

/-- Forgotten abelian form of the module-level weighting trace, before lifting
coefficients. -/
def weightingTraceModuleForgetHom {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule f Λ).obj ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj F)) ⟶
      (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F :=
  (lowerShriekModule_forget f Λ ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj F)).hom ≫
    (lowerShriek f).map
      ((etaleModuleSheafPullback_compSheafComposeIso f Λ).hom.app F) ≫
      weightingTrace f hw (etaleModuleForget Λ F)

/-- The underlying additive weighting trace preserves scalar multiplication. -/
theorem weightingTraceModuleForgetHom_map_smul
    {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (U : Y.Etaleᵒᵖ) (r : Λ)
    (x : ((lowerShriekModule f Λ).obj ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj F)).obj.obj U) :
    ((weightingTraceModuleForgetHom f Λ hw F).hom.app U).hom (r • x) =
      HSMul.hSMul (α := Λ) (β := F.obj.obj U)
        (γ := F.obj.obj U) r (((weightingTraceModuleForgetHom f Λ hw F).hom.app U).hom x) := sorry

/-- The sheaf-level `Λ`-linear weighting trace at a sheaf of modules. -/
def weightingTraceModuleHom {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule f Λ).obj ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj F) ⟶ F :=
  liftModuleSheafHom (weightingTraceModuleForgetHom f Λ hw F)
    (weightingTraceModuleForgetHom_map_smul f Λ hw F)

/-- Weighting traces commute with morphisms of module sheaves. -/
theorem weightingTraceModule_natural {w : X → ℤ} (hw : f.IsWeighting w)
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)} (φ : F ⟶ G) :
    (lowerShriekModule f Λ).map
        ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).map φ) ≫
      weightingTraceModuleHom f Λ hw G = weightingTraceModuleHom f Λ hw F ≫ φ := sorry

/-- The `Λ`-linear weighting trace as a natural transformation
`f_! ∘ f⁻¹ ⟶ 𝟭` on étale sheaves of modules. -/
def weightingTraceModuleNatTrans {w : X → ℤ} (hw : f.IsWeighting w) :
    Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ) ⋙ lowerShriekModule f Λ ⟶
      𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) where
  app F := weightingTraceModuleHom f Λ hw F
  naturality := fun _ _ φ ↦ weightingTraceModule_natural f Λ hw φ

/-- Components of `weightingTraceModuleNatTrans` are `weightingTraceModuleHom`. -/
theorem weightingTraceModuleNatTrans_app {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (weightingTraceModuleNatTrans f Λ hw).app F =
      weightingTraceModuleHom f Λ hw F := sorry

variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g').op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f').op]

/-- Forgetting coefficients identifies the module-level compact-support
comparison `g⁻¹ f_! ≅ f'_! (g')⁻¹` with the abelian isomorphism
`lowerShriekBaseChangeIso`. -/
def weightingTraceModuleLowerShriekForgetIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj ((lowerShriekModule f Λ).obj F)) ≅
      (sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule f' Λ).obj ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F)) :=
  (etaleModuleSheafPullback_compSheafComposeIso g Λ).app
      ((lowerShriekModule f Λ).obj F) ≪≫
    (etaleAbelianSheafPullback g).mapIso (lowerShriekModule_forget f Λ F) ≪≫
    lowerShriekBaseChangeIso_app f g f' g' h_cart (etaleModuleForget Λ F) ≪≫
    (lowerShriek f').mapIso
      ((etaleModuleSheafPullback_compSheafComposeIso g' Λ).app F).symm ≪≫
    (lowerShriekModule_forget f' Λ ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F)).symm

/-- The forward module base-change comparison preserves scalar multiplication. -/
theorem weightingTraceModuleLowerShriekHom_map_smul
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (U : Y'.Etaleᵒᵖ) (r : Λ)
    (x : ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj ((lowerShriekModule f Λ).obj F)).obj.obj U) :
    (((weightingTraceModuleLowerShriekForgetIso f Λ g f' g' h_cart F).hom).hom.app U).hom (r • x) =
      HSMul.hSMul (α := Λ) (β := ((lowerShriekModule f' Λ).obj
          ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F)).obj.obj U)
        (γ := ((lowerShriekModule f' Λ).obj
          ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F)).obj.obj U) r
          ((((weightingTraceModuleLowerShriekForgetIso f Λ g f' g' h_cart F).hom).hom.app U).hom x) := sorry

/-- The inverse module base-change comparison preserves scalar multiplication. -/
theorem weightingTraceModuleLowerShriekInv_map_smul
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (U : Y'.Etaleᵒᵖ) (r : Λ)
    (x : ((lowerShriekModule f' Λ).obj ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F)).obj.obj U) :
    (((weightingTraceModuleLowerShriekForgetIso f Λ g f' g' h_cart F).inv).hom.app U).hom (r • x) =
      HSMul.hSMul (α := Λ) (β := ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj ((lowerShriekModule f Λ).obj F)).obj.obj U)
        (γ := ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj ((lowerShriekModule f Λ).obj F)).obj.obj U) r
          ((((weightingTraceModuleLowerShriekForgetIso f Λ g f' g' h_cart F).inv).hom.app U).hom x) := sorry

/-- The forward linear comparison between compact-support module sheaves. -/
def weightingTraceModuleLowerShriekHom
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj ((lowerShriekModule f Λ).obj F) ⟶
      (lowerShriekModule f' Λ).obj ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F) :=
  liftModuleSheafHom (weightingTraceModuleLowerShriekForgetIso f Λ g f' g' h_cart F).hom
    (weightingTraceModuleLowerShriekHom_map_smul f Λ g f' g' h_cart F)

/-- The inverse linear comparison between compact-support module sheaves. -/
def weightingTraceModuleLowerShriekInv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule f' Λ).obj ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F) ⟶
      (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj ((lowerShriekModule f Λ).obj F) :=
  liftModuleSheafHom (weightingTraceModuleLowerShriekForgetIso f Λ g f' g' h_cart F).inv
    (weightingTraceModuleLowerShriekInv_map_smul f Λ g f' g' h_cart F)

/-- The forward-inverse comparison composite is the identity. -/
theorem weightingTraceModuleLowerShriekHom_inv_id
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    weightingTraceModuleLowerShriekHom f Λ g f' g' h_cart F ≫
      weightingTraceModuleLowerShriekInv f Λ g f' g' h_cart F =
        𝟙 ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj ((lowerShriekModule f Λ).obj F)) := sorry

/-- The inverse-forward comparison composite is the identity. -/
theorem weightingTraceModuleLowerShriekInv_hom_id
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    weightingTraceModuleLowerShriekInv f Λ g f' g' h_cart F ≫
      weightingTraceModuleLowerShriekHom f Λ g f' g' h_cart F =
        𝟙 ((lowerShriekModule f' Λ).obj ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F)) := sorry

/-- Module-level form of `lowerShriekBaseChangeIso_app`, obtained by lifting
the forgotten abelian identification along `forget₂`. -/
def weightingTraceModuleLowerShriekIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj ((lowerShriekModule f Λ).obj F) ≅
      (lowerShriekModule f' Λ).obj ((Sheaf.smallEtaleInverseImage g' (ModuleCat.{u} Λ)).obj F) where
  hom := weightingTraceModuleLowerShriekHom f Λ g f' g' h_cart F
  inv := weightingTraceModuleLowerShriekInv f Λ g f' g' h_cart F
  hom_inv_id := weightingTraceModuleLowerShriekHom_inv_id f Λ g f' g' h_cart F
  inv_hom_id := weightingTraceModuleLowerShriekInv_hom_id f Λ g f' g' h_cart F

/-- Sheaf-level left vertical identification of the module weighting-trace
base-change square: `g⁻¹ f_! f⁻¹ F ≅ f'_! (g')⁻¹ f⁻¹ F ≅ f'_! (f')⁻¹ g⁻¹ F`. -/
def weightingTraceModuleBaseChangeIso
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj
        ((lowerShriekModule f Λ).obj ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj F)) ≅
      (lowerShriekModule f' Λ).obj
        ((Sheaf.smallEtaleInverseImage f' (ModuleCat.{u} Λ)).obj
          ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj F)) :=
  (weightingTraceModuleLowerShriekIso f Λ g f' g' h_cart
      ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj F)).trans
    ((lowerShriekModule f' Λ).mapIso
      ((etaleModuleSheafPullback_square f g f' g' h_cart Λ).symm.app F))

/-- The forward map of `weightingTraceModuleBaseChangeIso` is the compact-support
comparison followed by `etaleModuleSheafPullback_square.symm`. -/
theorem weightingTraceModuleBaseChangeIso_hom
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (weightingTraceModuleBaseChangeIso f Λ g f' g' h_cart F).hom =
      (weightingTraceModuleLowerShriekIso f Λ g f' g' h_cart
          ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj F)).hom ≫
        (lowerShriekModule f' Λ).map
          ((etaleModuleSheafPullback_square f g f' g' h_cart Λ).inv.app F) := sorry

/-- The module trace-domain base-change isomorphisms are natural in the sheaf. -/
theorem weightingTraceModuleBaseChangeIso_naturality
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)} (φ : F ⟶ G) :
    (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).map
        ((lowerShriekModule f Λ).map
          ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).map φ)) ≫
      (weightingTraceModuleBaseChangeIso f Λ g f' g' h_cart G).hom =
    (weightingTraceModuleBaseChangeIso f Λ g f' g' h_cart F).hom ≫
      (lowerShriekModule f' Λ).map
        ((Sheaf.smallEtaleInverseImage f' (ModuleCat.{u} Λ)).map
          ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).map φ)) := sorry

/-- Natural isomorphism packaging of `weightingTraceModuleBaseChangeIso`. -/
def weightingTraceModuleBaseChangeNatIso :
    Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ) ⋙ lowerShriekModule f Λ ⋙
        Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ) ≅
      Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ) ⋙ Sheaf.smallEtaleInverseImage f' (ModuleCat.{u} Λ) ⋙
        lowerShriekModule f' Λ :=
  NatIso.ofComponents
    (fun F ↦ weightingTraceModuleBaseChangeIso f Λ g f' g' h_cart F)
    (fun {_ _} φ ↦ weightingTraceModuleBaseChangeIso_naturality f Λ g f' g' h_cart φ)

/-- Linear weighting traces commute with arbitrary cartesian base change. -/
theorem weightingTraceModule_baseChange {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).map
        (weightingTraceModuleHom f Λ hw F) =
      (weightingTraceModuleBaseChangeIso f Λ g f' g' h_cart F).hom ≫
        weightingTraceModuleHom f' Λ (w := fun x' ↦ w (g' x'))
          (IsWeighting.of_isPullback hw h_cart)
          ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj F) := sorry

end AlgebraicGeometry.Scheme.Etale

end
