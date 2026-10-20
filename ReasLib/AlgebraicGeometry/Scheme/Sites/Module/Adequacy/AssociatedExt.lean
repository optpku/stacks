/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Ambient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.AffineEquivalence
public import ReasLib.Algebra.Category.ModuleCat.PureExt
public import ReasLib.Algebra.Category.ModuleCat.PureInjective.Resolution.Adeq
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.TensorExtension

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe w u

namespace SheafOfModules.AffineAdeq

/-- The adequate module sheaf corresponding to an adequate module-valued functor under
affine evaluation. -/
noncomputable def adequateRealization (τ : StandardTopology) (A : CommRingCat.{u}) :
    ModuleValuedFunctor.TensorAdeq A ⥤ SheafOfModules.AffineAdeq τ A :=
  (SheafOfModules.affineEvaluationAdequate τ A).asEquivalence.inverse

/-- Affine evaluation of an adequately realized functor is canonically isomorphic to the
original adequate module-valued functor. -/
noncomputable def evaluationRealizationIso (τ : StandardTopology) (A : CommRingCat.{u}) :
    adequateRealization τ A ⋙ SheafOfModules.affineEvaluationAdequate τ A ≅
      𝟭 (ModuleValuedFunctor.TensorAdeq A) :=
  (SheafOfModules.affineEvaluationAdequate τ A).asEquivalence.counitIso

/-- A functorial realization equipped with an affine-evaluation specification is naturally
isomorphic to `adequateRealization`. -/
noncomputable def adequateRealizationIso
    (τ : StandardTopology) (A : CommRingCat.{u})
    (G : ModuleValuedFunctor.TensorAdeq A ⥤ SheafOfModules.AffineAdeq τ A)
    (evaluationIso : G ⋙ SheafOfModules.affineEvaluationAdequate τ A ≅
      𝟭 (ModuleValuedFunctor.TensorAdeq A)) :
    G ≅ adequateRealization τ A :=
  Functor.fullyFaithfulCancelRight (SheafOfModules.affineEvaluationAdequate τ A)
    (evaluationIso ≪≫ (evaluationRealizationIso τ A).symm)

/-- The component of `evaluationRealizationIso` is the counit of the affine-evaluation
equivalence. -/
theorem evaluationRealizationIso_hom_app
    (τ : StandardTopology) (A : CommRingCat.{u}) (F : ModuleValuedFunctor.TensorAdeq A) :
    (evaluationRealizationIso τ A).hom.app F =
      (SheafOfModules.affineEvaluationAdequate τ A).asEquivalence.counit.app F := sorry

/-- Realization of an adequate module-valued functor as a module sheaf on the big
`τ`-site of `Spec A`. -/
noncomputable def realization (τ : StandardTopology) (A : CommRingCat.{u}) :
    ModuleValuedFunctor.TensorAdeq A ⥤ RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))) :=
  adequateRealization τ A ⋙ inclusion τ A

/-- Affine realization is additive. -/
theorem realizationAdditive (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))] :
    @Functor.Additive
      (ModuleValuedFunctor.TensorAdeq A)
      (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
      _ _ Abelian.toPreadditive Abelian.toPreadditive
      (realization τ A) := sorry

/-- Affine realization preserves finite limits. -/
theorem realizationPreservesFiniteLimits
    (τ : StandardTopology) (A : CommRingCat.{u}) :
    PreservesFiniteLimits (realization τ A) := sorry

/-- Affine realization preserves finite colimits. -/
theorem realizationPreservesFiniteColimits
    (τ : StandardTopology) (A : CommRingCat.{u}) :
    PreservesFiniteColimits (realization τ A) := sorry

end SheafOfModules.AffineAdeq

namespace ModuleCat.PureExt

/-- The canonical associated big-site module sheaf functor `M ↦ Mᵃ` on `Spec A`. -/
noncomputable def associatedModule (τ : StandardTopology) (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))) :=
  (AlgebraicGeometry.tildeEquiv :
      ModuleCat.{u} A ≌ Scheme.QCoh (Scheme.Spec.obj (op A))).functor ⋙
    Scheme.AssociatedModule.bigModuleFunctor (Scheme.Spec.obj (op A)) τ

/-- The value of `associatedModule` is the established big-site associated module of the
quasi-coherent sheaf corresponding to the original module. -/
theorem associatedModule_obj (τ : StandardTopology) (A : CommRingCat.{u})
    (M : ModuleCat.{u} A) :
    (associatedModule τ A).obj M =
      (Scheme.AssociatedModule.bigModuleFunctor (Scheme.Spec.obj (op A)) τ).obj
        ((AlgebraicGeometry.tildeEquiv :
          ModuleCat.{u} A ≌ Scheme.QCoh (Scheme.Spec.obj (op A))).functor.obj M) := sorry

/-- Canonical associated big-site modules have adequate affine evaluation. -/
theorem canonicalAssociatedModule_adequate
    (τ : StandardTopology) (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    ModuleValuedFunctor.TensorAdequate
      (SheafOfModules.affineEvaluation
        ((associatedModule τ A).obj M).val A
          (𝟙 (Scheme.Spec.obj (op A)))) := sorry

/-- The canonical associated-module functor lifted to adequately evaluated sheaves. -/
noncomputable def canonicalAssociatedModuleAdeq
    (τ : StandardTopology) (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ SheafOfModules.AffineAdeq τ A :=
  ObjectProperty.lift _ (associatedModule τ A)
    (canonicalAssociatedModule_adequate τ A)

/-- Affine evaluation of the canonical associated module at an `A`-algebra `B` is the
corresponding scalar extension of the original module. -/
noncomputable def canonicalEvaluationIsoAppObj
    (τ : StandardTopology) (A : CommRingCat.{u})
    (M : ModuleCat.{u} A) (B : Under A) :
    ((((canonicalAssociatedModuleAdeq τ A ⋙
      SheafOfModules.affineEvaluationAdequate τ A).obj M).obj).obj B) ≅
      ((((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M).obj).obj B) :=
  (AlgebraicGeometry.moduleSpecΓFunctor (R := B.right)).mapIso
      ((AlgebraicGeometry.tilde.ChangeOfRings.Pullback.iso B.hom).app M) ≪≫
    (AlgebraicGeometry.tilde.isoTop
      ((ModuleCat.extendScalars B.hom.hom).obj M)).symm

/-- The forward comparison from affine evaluation of the canonical associated module to
tensor extension, assembled from the objectwise affine comparisons. -/
noncomputable def canonicalEvaluationHom
    (τ : StandardTopology) (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    (((canonicalAssociatedModuleAdeq τ A ⋙
      SheafOfModules.affineEvaluationAdequate τ A).obj M).obj) ⟶
      (((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M).obj) where
  app B := (canonicalEvaluationIsoAppObj τ A M B).hom
  naturality := sorry

/-- The inverse comparison from tensor extension to affine evaluation of the canonical
associated module. -/
noncomputable def canonicalEvaluationInv
    (τ : StandardTopology) (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    (((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M).obj) ⟶
      (((canonicalAssociatedModuleAdeq τ A ⋙
        SheafOfModules.affineEvaluationAdequate τ A).obj M).obj) where
  app B := (canonicalEvaluationIsoAppObj τ A M B).inv
  naturality := sorry

/-- The forward and inverse affine-evaluation comparisons compose to the identity. -/
theorem canonicalEvaluation_hom_inv_id
    (τ : StandardTopology) (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    canonicalEvaluationHom τ A M ≫ canonicalEvaluationInv τ A M = 𝟙 _ := sorry

/-- The inverse and forward affine-evaluation comparisons compose to the identity. -/
theorem canonicalEvaluation_inv_hom_id
    (τ : StandardTopology) (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    canonicalEvaluationInv τ A M ≫ canonicalEvaluationHom τ A M = 𝟙 _ := sorry

/-- Affine evaluation of the canonical associated module agrees explicitly with tensor
extension, for a fixed module. -/
noncomputable def canonicalEvaluationIsoApp
    (τ : StandardTopology) (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    (canonicalAssociatedModuleAdeq τ A ⋙
      SheafOfModules.affineEvaluationAdequate τ A).obj M ≅
        (ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M :=
  ObjectProperty.isoMk _
    { hom := canonicalEvaluationHom τ A M
      inv := canonicalEvaluationInv τ A M
      hom_inv_id := canonicalEvaluation_hom_inv_id τ A M
      inv_hom_id := canonicalEvaluation_inv_hom_id τ A M }

/-- The fixed-module affine-evaluation isomorphisms are natural in the module. -/
theorem canonicalEvaluationIsoApp_naturality
    (τ : StandardTopology) (A : CommRingCat.{u}) {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (canonicalAssociatedModuleAdeq τ A ⋙
        SheafOfModules.affineEvaluationAdequate τ A).map f ≫
      (canonicalEvaluationIsoApp τ A N).hom =
      (canonicalEvaluationIsoApp τ A M).hom ≫
        (ModuleValuedFunctor.TensorAdeq.tensorExtension A).map f := sorry

/-- Affine evaluation of the canonical associated-module functor is naturally isomorphic to
tensor extension. -/
noncomputable def canonicalEvaluationIso
    (τ : StandardTopology) (A : CommRingCat.{u}) :
    canonicalAssociatedModuleAdeq τ A ⋙
      SheafOfModules.affineEvaluationAdequate τ A ≅
        ModuleValuedFunctor.TensorAdeq.tensorExtension A :=
  NatIso.ofComponents (canonicalEvaluationIsoApp τ A)
    (fun f ↦ canonicalEvaluationIsoApp_naturality τ A f)

/-- The realization-model module sheaf functor obtained from tensor extension and an inverse
to affine evaluation. -/
noncomputable def realizedAssociatedModule (τ : StandardTopology) (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))) :=
  ModuleValuedFunctor.TensorAdeq.tensorExtension A ⋙
    SheafOfModules.AffineAdeq.realization τ A

/-- The canonical adequately evaluated associated-module functor is naturally isomorphic to
the inverse-affine-evaluation realization of tensor extension. -/
noncomputable def canonicalAdequateIso
    (τ : StandardTopology) (A : CommRingCat.{u}) :
    canonicalAssociatedModuleAdeq τ A ≅
      ModuleValuedFunctor.TensorAdeq.tensorExtension A ⋙
        SheafOfModules.AffineAdeq.adequateRealization τ A :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (canonicalAssociatedModuleAdeq τ A)
      (SheafOfModules.affineEvaluationAdequate τ A).asEquivalence.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (canonicalEvaluationIso τ A)
      (SheafOfModules.affineEvaluationAdequate τ A).asEquivalence.inverse

/-- The realization model of `Mᵃ` is naturally isomorphic to the canonical associated-module
functor. -/
noncomputable def associatedModuleIso (τ : StandardTopology) (A : CommRingCat.{u}) :
    realizedAssociatedModule τ A ≅ associatedModule τ A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (canonicalAdequateIso τ A).symm
      (SheafOfModules.AffineAdeq.inclusion τ A)

/-- The realization-model associated module of `M` realizes its tensor-extension functor. -/
theorem realizedAssociatedModule_obj (τ : StandardTopology) (A : CommRingCat.{u})
    (M : ModuleCat.{u} A) :
    (realizedAssociatedModule τ A).obj M =
      (SheafOfModules.AffineAdeq.realization τ A).obj
        ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M) := sorry


/-- The bifunctor of ambient sheaf extension groups between realization-model module
sheaves on `Spec A`. -/
noncomputable def realizedSheafFunctor (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    (i : ℕ) :
    (ModuleCat.{u} A)ᵒᵖ ⥤ ModuleCat.{u} A ⥤ AddCommGrpCat.{w} :=
  (((Functor.whiskeringLeft₂ AddCommGrpCat.{w}).obj
    (realizedAssociatedModule τ A).op).obj (realizedAssociatedModule τ A)).obj
      (Abelian.extFunctor
        (C := RingedSite.ModuleCat.{u}
          (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A)))) i)

/-- The bifunctor of ambient sheaf extension groups between associated modules on `Spec A`. -/
noncomputable def sheafFunctor (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    (i : ℕ) :
    (ModuleCat.{u} A)ᵒᵖ ⥤ ModuleCat.{u} A ⥤ AddCommGrpCat.{w} :=
  (((Functor.whiskeringLeft₂ AddCommGrpCat.{w}).obj
    (associatedModule τ A).op).obj (associatedModule τ A)).obj
      (Abelian.extFunctor
        (C := RingedSite.ModuleCat.{u}
          (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A)))) i)

/-- Transporting both Ext arguments along `associatedModuleIso` identifies the
realization-model and canonical associated-module Ext bifunctors. -/
noncomputable def sheafFunctorIso (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    (i : ℕ) : realizedSheafFunctor τ A i ≅ sheafFunctor τ A i :=
  (((Functor.whiskeringLeft₂ AddCommGrpCat.{w}).mapIso
      (NatIso.op (associatedModuleIso τ A).symm)).app
        (realizedAssociatedModule τ A)).app
      (Abelian.extFunctor
        (C := RingedSite.ModuleCat.{u}
          (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A)))) i) ≪≫
    ((((Functor.whiskeringLeft₂ AddCommGrpCat.{w}).obj
      (associatedModule τ A).op).mapIso (associatedModuleIso τ A)).app
        (Abelian.extFunctor
          (C := RingedSite.ModuleCat.{u}
            (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A)))) i))

/-- Evaluation of `sheafFunctor τ A i` is ambient Ext between the associated module
sheaves. -/
theorem sheafFunctor_obj_obj (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    (i : ℕ) (M N : ModuleCat.{u} A) :
    ((sheafFunctor τ A i).obj (op M)).obj N =
      AddCommGrpCat.of
        (Abelian.Ext ((associatedModule τ A).obj M)
          ((associatedModule τ A).obj N) i) := sorry

/-- The Ext maps induced by affine realization are natural in the covariant module
argument. -/
theorem realizedComparisonApp_naturality (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)]
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [hRealAdd : @Functor.Additive
      (ModuleValuedFunctor.TensorAdeq A)
      (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
      _ _ Abelian.toPreadditive Abelian.toPreadditive
      (SheafOfModules.AffineAdeq.realization τ A)]
    [hLim : PreservesFiniteLimits (SheafOfModules.AffineAdeq.realization τ A)]
    [hColim : PreservesFiniteColimits (SheafOfModules.AffineAdeq.realization τ A)]
    (i : ℕ) (M : (ModuleCat.{u} A)ᵒᵖ) {N N' : ModuleCat.{u} A} (f : N ⟶ N') :
    ((functor A i).obj M).map f ≫
        AddCommGrpCat.ofHom
          (@Functor.mapExtAddHom _ _ _ _ _ _
            (SheafOfModules.AffineAdeq.realization τ A)
            (hRealAdd : @Functor.Additive
              (ModuleValuedFunctor.TensorAdeq A)
              (RingedSite.ModuleCat.{u}
                (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
              _ _ Abelian.toPreadditive Abelian.toPreadditive
              (SheafOfModules.AffineAdeq.realization τ A))
            hLim hColim _ _
            ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M.unop)
            ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj N') i) =
      AddCommGrpCat.ofHom
          (@Functor.mapExtAddHom _ _ _ _ _ _
            (SheafOfModules.AffineAdeq.realization τ A)
            (hRealAdd : @Functor.Additive
              (ModuleValuedFunctor.TensorAdeq A)
              (RingedSite.ModuleCat.{u}
                (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
              _ _ Abelian.toPreadditive Abelian.toPreadditive
              (SheafOfModules.AffineAdeq.realization τ A))
            hLim hColim _ _
            ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M.unop)
            ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj N) i) ≫
        ((realizedSheafFunctor τ A i).obj M).map f := sorry

/-- For a fixed first argument, the component of the pure-Ext comparison induced by affine
realization. -/
noncomputable def realizedComparisonApp (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)]
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [hRealAdd : @Functor.Additive
      (ModuleValuedFunctor.TensorAdeq A)
      (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
      _ _ Abelian.toPreadditive Abelian.toPreadditive
      (SheafOfModules.AffineAdeq.realization τ A)]
    [hLim : PreservesFiniteLimits (SheafOfModules.AffineAdeq.realization τ A)]
    [hColim : PreservesFiniteColimits (SheafOfModules.AffineAdeq.realization τ A)]
    (i : ℕ) (M : (ModuleCat.{u} A)ᵒᵖ) :
    (functor A i).obj M ⟶ (realizedSheafFunctor τ A i).obj M where
  app N := AddCommGrpCat.ofHom
    (@Functor.mapExtAddHom _ _ _ _ _ _
      (SheafOfModules.AffineAdeq.realization τ A)
            (hRealAdd : @Functor.Additive
              (ModuleValuedFunctor.TensorAdeq A)
              (RingedSite.ModuleCat.{u}
                (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
              _ _ Abelian.toPreadditive Abelian.toPreadditive
              (SheafOfModules.AffineAdeq.realization τ A))
            hLim hColim _ _
      ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M.unop)
      ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj N) i)
  naturality := fun {_ _} f ↦ realizedComparisonApp_naturality τ A i M f

/-- The fixed-first-argument comparisons are natural in the contravariant module argument. -/
theorem realizedComparison_naturality (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)]
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [hRealAdd : @Functor.Additive
      (ModuleValuedFunctor.TensorAdeq A)
      (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
      _ _ Abelian.toPreadditive Abelian.toPreadditive
      (SheafOfModules.AffineAdeq.realization τ A)]
    [hLim : PreservesFiniteLimits (SheafOfModules.AffineAdeq.realization τ A)]
    [hColim : PreservesFiniteColimits (SheafOfModules.AffineAdeq.realization τ A)]
    (i : ℕ) {M M' : (ModuleCat.{u} A)ᵒᵖ} (f : M ⟶ M') :
    (functor A i).map f ≫ realizedComparisonApp τ A i M' =
      realizedComparisonApp τ A i M ≫ (realizedSheafFunctor τ A i).map f := sorry

/-- The realization-induced natural map from pure extension groups to extension groups of the
realization-model module sheaves. -/
noncomputable def realizedComparison (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)]
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [hRealAdd : @Functor.Additive
      (ModuleValuedFunctor.TensorAdeq A)
      (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
      _ _ Abelian.toPreadditive Abelian.toPreadditive
      (SheafOfModules.AffineAdeq.realization τ A)]
    [hLim : PreservesFiniteLimits (SheafOfModules.AffineAdeq.realization τ A)]
    [hColim : PreservesFiniteColimits (SheafOfModules.AffineAdeq.realization τ A)]
    (i : ℕ) : functor A i ⟶ realizedSheafFunctor τ A i where
  app M := realizedComparisonApp τ A i M
  naturality := fun {_ _} f ↦ realizedComparison_naturality τ A i f

/-- The canonical natural map from pure extension groups to extension groups of the
canonical associated module sheaves. -/
noncomputable def comparison (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)]
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [hRealAdd : @Functor.Additive
      (ModuleValuedFunctor.TensorAdeq A)
      (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
      _ _ Abelian.toPreadditive Abelian.toPreadditive
      (SheafOfModules.AffineAdeq.realization τ A)]
    [hLim : PreservesFiniteLimits (SheafOfModules.AffineAdeq.realization τ A)]
    [hColim : PreservesFiniteColimits (SheafOfModules.AffineAdeq.realization τ A)]
    (i : ℕ) : functor A i ⟶ sheafFunctor τ A i :=
  realizedComparison τ A i ≫ (sheafFunctorIso τ A i).hom

/-- The component of `comparison` is the map on Ext induced by affine realization,
transported along the natural isomorphism to the canonical associated modules. -/
theorem comparison_app (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)]
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [hRealAdd : @Functor.Additive
      (ModuleValuedFunctor.TensorAdeq A)
      (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
      _ _ Abelian.toPreadditive Abelian.toPreadditive
      (SheafOfModules.AffineAdeq.realization τ A)]
    [hLim : PreservesFiniteLimits (SheafOfModules.AffineAdeq.realization τ A)]
    [hColim : PreservesFiniteColimits (SheafOfModules.AffineAdeq.realization τ A)]
    (i : ℕ) (M N : ModuleCat.{u} A) :
    ((comparison τ A i).app (op M)).app N =
      AddCommGrpCat.ofHom
        (@Functor.mapExtAddHom _ _ _ _ _ _
          (SheafOfModules.AffineAdeq.realization τ A)
            (hRealAdd : @Functor.Additive
              (ModuleValuedFunctor.TensorAdeq A)
              (RingedSite.ModuleCat.{u}
                (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
              _ _ Abelian.toPreadditive Abelian.toPreadditive
              (SheafOfModules.AffineAdeq.realization τ A))
            hLim hColim _ _
          ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M)
          ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj N) i) ≫
        (((sheafFunctorIso τ A i).hom.app (op M)).app N) := sorry

/-- Transport of a chosen-resolution computation of pure Ext along the associated-module
comparison. -/
noncomputable def comparison_mapPureExt (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [hRealAdd : @Functor.Additive
      (ModuleValuedFunctor.TensorAdeq A)
      (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
      _ _ Abelian.toPreadditive Abelian.toPreadditive
      (SheafOfModules.AffineAdeq.realization τ A)]
    [hLim : PreservesFiniteLimits (SheafOfModules.AffineAdeq.realization τ A)]
    [hColim : PreservesFiniteColimits (SheafOfModules.AffineAdeq.realization τ A)]
    [UnivLE.{u, w}]
    {N : ModuleCat.{u} A} (I : PureInjectiveCoresolution N)
    (M : ModuleCat.{u} A) (i : ℕ) :
    AddCommGrpCat.of (Shrink.{w} (I.pureExt M i : Type u)) ⟶
      ((sheafFunctor τ A i).obj (op M)).obj N :=
  I.resolutionComparison M i ≫ ((comparison τ A i).app (op M)).app N

/-- The canonical natural map from functorial pure extension groups to extension groups of
associated module sheaves is an isomorphism. -/
theorem comparisonIsIso (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)]
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [hRealAdd : @Functor.Additive
      (ModuleValuedFunctor.TensorAdeq A)
      (RingedSite.ModuleCat.{u}
        (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))
      _ _ Abelian.toPreadditive Abelian.toPreadditive
      (SheafOfModules.AffineAdeq.realization τ A)]
    [hLim : PreservesFiniteLimits (SheafOfModules.AffineAdeq.realization τ A)]
    [hColim : PreservesFiniteColimits (SheafOfModules.AffineAdeq.realization τ A)]
    (i : ℕ) : IsIso (comparison τ A i) := sorry

end ModuleCat.PureExt
