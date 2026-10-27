/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.Weighting.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import stacks_project.Chap63.Lemma_63_4_10
public import stacks_project.Chap63.Lemma_63_5_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_5_2
public import stacks_project.Chap63.Lemma_63_7_1_Adjunction
public import stacks_project.Chap63.Lemma_63_8_5_Pullback

/-!
# Functoriality, base change, and derived weighting traces

The sheaf-level weighting trace `Tr_{f, w, F}` is packaged as a natural
transformation, compared with its cartesian base change, and lifted to
`Tr_{f, w, K}` on `D(Y_étale, Λ)` by applying the exact functors `f_!` and
`f⁻¹` to representing complexes of `Λ`-modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y X' Y' : Scheme.{u}}
variable {f : X ⟶ Y} [LocallyQuasiFinite f]
variable {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

#check (AlgebraicGeometry.Scheme.Hom.IsWeighting.of_isPullback :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w) [LocallyQuasiFinite f']
    (h_cart : IsPullback g' f' f g), f'.IsWeighting (fun x' ↦ w (g' x')))

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceNatTrans f :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w),
    etaleAbelianSheafPullback f ⋙ lowerShriek f ⟶
      𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceNatTrans_app f :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}),
    (weightingTraceNatTrans f hw).app F = weightingTrace f hw F)

variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceBaseChangeIso f g f' g' h_cart :
  ∀ (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}),
    (etaleAbelianSheafPullback g).obj
        ((lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F)) ≅
      (lowerShriek f').obj
        ((etaleAbelianSheafPullback f').obj
          ((etaleAbelianSheafPullback g).obj F)))

#check (AlgebraicGeometry.Scheme.Etale.weightingTrace_isPullback f g f' g' h_cart :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u}),
    (lowerShriek f').obj ((etaleAbelianSheafPullback f').obj F) ⟶ F)

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceBaseChangeIso_hom f g f' g' h_cart :
  ∀ (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}),
    (weightingTraceBaseChangeIso f g f' g' h_cart F).hom =
      (lowerShriekBaseChangeIso_app f g f' g' h_cart
          ((etaleAbelianSheafPullback f).obj F)).hom ≫
        (lowerShriek f').map
          ((etaleAbelianSheafPullback_square f g f' g' h_cart).inv.app F))

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

variable (Λ : Type u) [CommRing Λ]
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

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceModuleForgetHom f Λ :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)),
    (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule f Λ).obj ((etaleModuleSheafPullback f Λ).obj F)) ⟶
      (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceModuleHom f Λ :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)),
    (lowerShriekModule f Λ).obj ((etaleModuleSheafPullback f Λ).obj F) ⟶ F)

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceModuleNatTrans f Λ :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w),
    etaleModuleSheafPullback f Λ ⋙ lowerShriekModule f Λ ⟶
      𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceModuleNatTrans_app f Λ :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)),
    (weightingTraceModuleNatTrans f Λ hw).app F =
      weightingTraceModuleHom f Λ hw F)

variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceDerivedNatTrans f Λ :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w),
    etaleModuleDerivedInverseImage f Λ ⋙ lowerShriekModuleDerived f Λ ⟶
      𝟭 (EtaleDerived Y Λ))

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceDerived f Λ :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    (K : EtaleDerived Y Λ),
    (lowerShriekModuleDerived f Λ).obj
        ((etaleModuleDerivedInverseImage f Λ).obj K) ⟶ K)

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceDerived_natural f Λ :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    {K L : EtaleDerived Y Λ} (φ : K ⟶ L),
    (lowerShriekModuleDerived f Λ).map
          ((etaleModuleDerivedInverseImage f Λ).map φ) ≫
        weightingTraceDerived f Λ hw L =
      weightingTraceDerived f Λ hw K ≫ φ)

section DerivedBaseChange

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
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceModuleLowerShriekForgetIso f Λ g f' g' h_cart :
  ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)),
    (sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((etaleModuleSheafPullback g Λ).obj ((lowerShriekModule f Λ).obj F)) ≅
      (sheafCompose Y'.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule f' Λ).obj ((etaleModuleSheafPullback g' Λ).obj F)))

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceModuleLowerShriekIso f Λ g f' g' h_cart :
  ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)),
    (etaleModuleSheafPullback g Λ).obj ((lowerShriekModule f Λ).obj F) ≅
      (lowerShriekModule f' Λ).obj ((etaleModuleSheafPullback g' Λ).obj F))

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceModuleBaseChangeIso f Λ g f' g' h_cart :
  ∀ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)),
    (etaleModuleSheafPullback g Λ).obj
        ((lowerShriekModule f Λ).obj ((etaleModuleSheafPullback f Λ).obj F)) ≅
      (lowerShriekModule f' Λ).obj
        ((etaleModuleSheafPullback f' Λ).obj
          ((etaleModuleSheafPullback g Λ).obj F)))

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceModuleBaseChangeIso_hom f Λ g f' g' h_cart :
  ∀ (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)),
    (weightingTraceModuleBaseChangeIso f Λ g f' g' h_cart F).hom =
      (weightingTraceModuleLowerShriekIso f Λ g f' g' h_cart
          ((etaleModuleSheafPullback f Λ).obj F)).hom ≫
        (lowerShriekModule f' Λ).map
          ((etaleModuleSheafPullback_square f g f' g' h_cart Λ).inv.app F))

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceModuleBaseChangeNatIso f Λ g f' g' h_cart :
  etaleModuleSheafPullback f Λ ⋙ lowerShriekModule f Λ ⋙
        etaleModuleSheafPullback g Λ ≅
      etaleModuleSheafPullback g Λ ⋙ etaleModuleSheafPullback f' Λ ⋙
        lowerShriekModule f' Λ)

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceDerivedBaseChangeIso f Λ g f' g' h_cart :
  ∀ (K : EtaleDerived Y Λ),
    (etaleModuleDerivedInverseImage g Λ).obj
        ((lowerShriekModuleDerived f Λ).obj
          ((etaleModuleDerivedInverseImage f Λ).obj K)) ≅
      (lowerShriekModuleDerived f' Λ).obj
        ((etaleModuleDerivedInverseImage f' Λ).obj
          ((etaleModuleDerivedInverseImage g Λ).obj K)))

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceDerived_isPullback f Λ g f' g' h_cart :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    (K : EtaleDerived Y' Λ),
    (lowerShriekModuleDerived f' Λ).obj
        ((etaleModuleDerivedInverseImage f' Λ).obj K) ⟶ K)

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceDerived_baseChange f Λ g f' g' h_cart :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    (K : EtaleDerived Y Λ),
    (etaleModuleDerivedInverseImage g Λ).map
        (weightingTraceDerived f Λ hw K) =
      (weightingTraceDerivedBaseChangeIso f Λ g f' g' h_cart K).hom ≫
        weightingTraceDerived_isPullback f Λ g f' g' h_cart hw
          ((etaleModuleDerivedInverseImage g Λ).obj K))

end DerivedBaseChange

end AlgebraicGeometry.Scheme.Etale

end
