/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.GeneralComposition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Forget
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.Weighting.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasCoproducts.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (f ≫ g)).op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (f ≫ g)).op]

/-- Forgetting coefficients identifies `(f ≫ g)_! F` with `g_! (f_! (forget F))`
via `lowerShriekFunctorCompIso`. -/
def weightingTraceModuleLowerShriekCompForgetIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Z.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule (f ≫ g) Λ).obj F) ≅
      (sheafCompose Z.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F)) :=
  lowerShriekModule_forget (f ≫ g) Λ F ≪≫
    (lowerShriekFunctorCompIso f g).app (etaleModuleForget Λ F) ≪≫
    (lowerShriek g).mapIso (lowerShriekModule_forget f Λ F).symm ≪≫
    (lowerShriekModule_forget g Λ ((lowerShriekModule f Λ).obj F)).symm

/-- The forward compact-support composition comparison preserves scalars. -/
theorem weightingTraceModuleLowerShriekCompHom_map_smul
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (U : Z.Etaleᵒᵖ) (r : Λ)
    (x : ((lowerShriekModule (f ≫ g) Λ).obj F).obj.obj U) :
    (((weightingTraceModuleLowerShriekCompForgetIso f g Λ F).hom).hom.app U).hom (r • x) =
      HSMul.hSMul (α := Λ) (β := ((lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F)).obj.obj U)
        (γ := ((lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F)).obj.obj U) r
          ((((weightingTraceModuleLowerShriekCompForgetIso f g Λ F).hom).hom.app U).hom x) := sorry

/-- The inverse compact-support composition comparison preserves scalars. -/
theorem weightingTraceModuleLowerShriekCompInv_map_smul
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (U : Z.Etaleᵒᵖ) (r : Λ)
    (x : ((lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F)).obj.obj U) :
    (((weightingTraceModuleLowerShriekCompForgetIso f g Λ F).inv).hom.app U).hom (r • x) =
      HSMul.hSMul (α := Λ) (β := ((lowerShriekModule (f ≫ g) Λ).obj F).obj.obj U)
        (γ := ((lowerShriekModule (f ≫ g) Λ).obj F).obj.obj U) r
          ((((weightingTraceModuleLowerShriekCompForgetIso f g Λ F).inv).hom.app U).hom x) := sorry

/-- The forward linear comparison between compact-support module sheaves. -/
def weightingTraceModuleLowerShriekCompHom
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule (f ≫ g) Λ).obj F ⟶ (lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F) :=
  liftModuleSheafHom (weightingTraceModuleLowerShriekCompForgetIso f g Λ F).hom
    (weightingTraceModuleLowerShriekCompHom_map_smul f g Λ F)

/-- The inverse linear comparison between compact-support module sheaves. -/
def weightingTraceModuleLowerShriekCompInv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F) ⟶ (lowerShriekModule (f ≫ g) Λ).obj F :=
  liftModuleSheafHom (weightingTraceModuleLowerShriekCompForgetIso f g Λ F).inv
    (weightingTraceModuleLowerShriekCompInv_map_smul f g Λ F)

/-- The forward-inverse comparison composite is the identity. -/
theorem weightingTraceModuleLowerShriekCompHom_inv_id
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    weightingTraceModuleLowerShriekCompHom f g Λ F ≫
      weightingTraceModuleLowerShriekCompInv f g Λ F =
        𝟙 ((lowerShriekModule (f ≫ g) Λ).obj F) := sorry

/-- The inverse-forward comparison composite is the identity. -/
theorem weightingTraceModuleLowerShriekCompInv_hom_id
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    weightingTraceModuleLowerShriekCompInv f g Λ F ≫
      weightingTraceModuleLowerShriekCompHom f g Λ F =
        𝟙 ((lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F)) := sorry

/-- Module-level form of `lowerShriekFunctorCompIso`, obtained by lifting the
forgotten abelian identification along `forget₂`. -/
def weightingTraceModuleLowerShriekCompIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule (f ≫ g) Λ).obj F ≅
      (lowerShriekModule g Λ).obj ((lowerShriekModule f Λ).obj F) where
  hom := weightingTraceModuleLowerShriekCompHom f g Λ F
  inv := weightingTraceModuleLowerShriekCompInv f g Λ F
  hom_inv_id := weightingTraceModuleLowerShriekCompHom_inv_id f g Λ F
  inv_hom_id := weightingTraceModuleLowerShriekCompInv_hom_id f g Λ F

/-- Sheaf-level identification
`(f ≫ g)_! (f ≫ g)⁻¹ F ≅ g_! f_! f⁻¹ g⁻¹ F` of étale sheaves of modules. -/
def weightingTraceModuleCompIso
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule (f ≫ g) Λ).obj
        ((Sheaf.smallEtaleInverseImage (f ≫ g) (ModuleCat.{u} Λ)).obj F) ≅
      (lowerShriekModule g Λ).obj
        ((lowerShriekModule f Λ).obj
          ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj
            ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj F))) :=
  (lowerShriekModule (f ≫ g) Λ).mapIso
      ((Hom.etaleModuleSheafPullback_comp Λ g f).symm.app F) ≪≫
    weightingTraceModuleLowerShriekCompIso f g Λ
      ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).obj ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).obj F))

/-- The module trace-domain composition comparison is natural in the sheaf. -/
theorem weightingTraceModuleCompIso_naturality
    {F G : Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)} (φ : F ⟶ G) :
    (lowerShriekModule (f ≫ g) Λ).map
        ((Sheaf.smallEtaleInverseImage (f ≫ g) (ModuleCat.{u} Λ)).map φ) ≫
      (weightingTraceModuleCompIso f g Λ G).hom =
    (weightingTraceModuleCompIso f g Λ F).hom ≫
      (lowerShriekModule g Λ).map ((lowerShriekModule f Λ).map
        ((Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).map
          ((Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).map φ))) := sorry

/-- Natural isomorphism packaging of `weightingTraceModuleCompIso`. -/
def weightingTraceModuleCompNatIso :
    Sheaf.smallEtaleInverseImage (f ≫ g) (ModuleCat.{u} Λ) ⋙ lowerShriekModule (f ≫ g) Λ ≅
      Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ) ⋙ Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ) ⋙
        lowerShriekModule f Λ ⋙ lowerShriekModule g Λ :=
  NatIso.ofComponents (weightingTraceModuleCompIso f g Λ)
    (fun {_ _} φ ↦ weightingTraceModuleCompIso_naturality f g Λ φ)

variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived identification `(f ≫ g)_! (f ≫ g)⁻¹ K ≅ g_! f_! f⁻¹ g⁻¹ K` on
`D(Z_étale, Λ)`, obtained by `ExactFunctor.MapDerivedCategory` of the
sheaf-level module identification after reassociating composites of exact
functors. -/
def weightingTraceDerivedCompIso (K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (lowerShriekModuleDerived (f ≫ g) Λ).obj
        ((etaleModuleDerivedInverseImage (f ≫ g) Λ).obj K) ≅
      (lowerShriekModuleDerived g Λ).obj
        ((lowerShriekModuleDerived f Λ).obj
          ((etaleModuleDerivedInverseImage f Λ).obj
            ((etaleModuleDerivedInverseImage g Λ).obj K))) :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (Sheaf.smallEtaleInverseImage (f ≫ g) (ModuleCat.{u} Λ)))
      (ExactFunctor.of (lowerShriekModule (f ≫ g) Λ))).symm.app K ≪≫
    Functor.MapDerivedCategory.objIso (weightingTraceModuleCompNatIso f g Λ) K ≪≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
        (ExactFunctor.of
          (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ) ⋙ Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ) ⋙
            lowerShriekModule f Λ))
        (ExactFunctor.of (lowerShriekModule g Λ))).app K ≪≫
    (lowerShriekModuleDerived g Λ).mapIso
      ((ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of
            (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ) ⋙ Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)))
          (ExactFunctor.of (lowerShriekModule f Λ))).app K) ≪≫
    (lowerShriekModuleDerived g Λ).mapIso
      ((lowerShriekModuleDerived f Λ).mapIso
        ((ExactFunctor.MapDerivedCategory.compFunctorIso
            (ExactFunctor.of (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)))
            (ExactFunctor.of (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)))).app K))

/-- The forward map of `weightingTraceDerivedCompIso` is the composite of the
exact-derived reassociations with `mapDerivedCategory` of
`weightingTraceModuleCompNatIso`. -/
theorem weightingTraceDerivedCompIso_hom (K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (weightingTraceDerivedCompIso f g Λ K).hom =
      (ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of (Sheaf.smallEtaleInverseImage (f ≫ g) (ModuleCat.{u} Λ)))
          (ExactFunctor.of (lowerShriekModule (f ≫ g) Λ))).inv.app K ≫
        (Functor.MapDerivedCategory.objIso
          (weightingTraceModuleCompNatIso f g Λ) K).hom ≫
        (ExactFunctor.MapDerivedCategory.compFunctorIso
            (ExactFunctor.of
              (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ) ⋙ Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ) ⋙
                lowerShriekModule f Λ))
            (ExactFunctor.of (lowerShriekModule g Λ))).hom.app K ≫
        (lowerShriekModuleDerived g Λ).map
          ((ExactFunctor.MapDerivedCategory.compFunctorIso
              (ExactFunctor.of
                (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ) ⋙ Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)))
              (ExactFunctor.of (lowerShriekModule f Λ))).hom.app K) ≫
        (lowerShriekModuleDerived g Λ).map
          ((lowerShriekModuleDerived f Λ).map
            ((ExactFunctor.MapDerivedCategory.compFunctorIso
                (ExactFunctor.of (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)))
                (ExactFunctor.of (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)))).hom.app K)) := sorry

/-- Derived weighting traces for composable locally quasi-finite morphisms compose
under the canonical compact-support and inverse-image comparison, with composite
weighting `fun x ↦ w_f x * w_g (f x)`. -/
theorem weightingTraceDerived_comp {w_f : X → ℤ} (hw_f : f.IsWeighting w_f)
    {w_g : Y → ℤ} (hw_g : g.IsWeighting w_g)
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (weightingTraceDerivedCompIso f g Λ K).hom ≫
      (lowerShriekModuleDerived g Λ).map
        (weightingTraceDerived f Λ hw_f
          ((etaleModuleDerivedInverseImage g Λ).obj K)) ≫
      weightingTraceDerived g Λ hw_g K =
      weightingTraceDerived (f ≫ g) Λ (w := fun x ↦ w_f x * w_g (f x))
        (IsWeighting.comp hw_f hw_g) K := sorry

end AlgebraicGeometry.Scheme.Etale

end
