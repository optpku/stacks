module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FlatPullbackSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.Tensor
public import ReasLib.CategoryTheory.Monoidal.Adjunction.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator.HomotopyLimit.Thickenings

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open DerivedTensor.Right
open RingedSite.Hom.DerivedAdjunction
open RingedSpace.ModuleDerived.KFlat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The stage identification of a quasicoherent system, followed by the canonical
degree-zero comparison from ordinary to derived pushforward. -/
noncomputable def thickeningSystemStageMap
    {X Y : Scheme.{u}} (p : Y ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    (F : SequentialInverseSystem (Scheme.QCoh X))
    (G : Y.Modules) [G.IsQuasicoherent]
    (n : ℕ) (stageIso : F.obj (Opposite.op n) ≅
      (Scheme.QCoh.pushforward p).obj (⟨G, inferInstance⟩ : Scheme.QCoh Y))
    :
    ((F ⋙ Scheme.QCoh.inclusion X ⋙
      DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
        (Opposite.op n)) ⟶
      (RingedSpace.moduleDerivedPushforward p.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) :=
  (DerivedCategory.singleFunctor X.Modules 0).map stageIso.hom.hom ≫
    RingedSpace.moduleDerivedPushforward.comparison p.toShHom
      ((Scheme.QCoh.pushforward p).obj
        (⟨G, inferInstance⟩ : Scheme.QCoh Y)).obj G
      ((Scheme.QCoh.pushforward.inclusionIso p).hom.app
        (⟨G, inferInstance⟩ : Scheme.QCoh Y))

/-- `thickeningSystemStageMap` is the stage isomorphism followed by the canonical
single-complex pushforward comparison. -/
theorem thickeningSystemStageMap_def
    {X Y : Scheme.{u}} (p : Y ⟶ X) [QuasiCompact p] [QuasiSeparated p]
    (F : SequentialInverseSystem (Scheme.QCoh X))
    (G : Y.Modules) [G.IsQuasicoherent]
    (n : ℕ) (stageIso : F.obj (Opposite.op n) ≅
      (Scheme.QCoh.pushforward p).obj (⟨G, inferInstance⟩ : Scheme.QCoh Y))
    :
    thickeningSystemStageMap p F G n stageIso =
      (DerivedCategory.singleFunctor X.Modules 0).map stageIso.hom.hom ≫
        RingedSpace.moduleDerivedPushforward.comparison p.toShHom
          ((Scheme.QCoh.pushforward p).obj
            (⟨G, inferInstance⟩ : Scheme.QCoh Y)).obj G
          ((Scheme.QCoh.pushforward.inclusionIso p).hom.app
            (⟨G, inferInstance⟩ : Scheme.QCoh Y)) := sorry

/-- The canonical map from a presented limit to a stage, followed by a specified
identification of that stage with a derived pushforward. -/
noncomputable def limitToStagePushforward
    {X Y : Scheme.{u}} (p : Y ⟶ X)
    {T : SequentialInverseSystem (RingedSpace.ModuleDerived X.toRingedSpace)}
    {Klim K : RingedSpace.ModuleDerived X.toRingedSpace}
    (P : HomotopyLimit.Presentation T Klim) (n : ℕ)
    (G : Y.Modules) (toLimit : K ⟶ Klim)
    (stage : T.obj (Opposite.op n) ⟶
      (RingedSpace.moduleDerivedPushforward p.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) :
    K ⟶ (RingedSpace.moduleDerivedPushforward p.toShHom).obj
      ((DerivedCategory.singleFunctor Y.Modules 0).obj G) :=
  toLimit ≫ P.stageProjection n ≫ stage

/-- Pulling the limit-to-stage map across the derived pullback-pushforward adjunction
gives the canonical comparison on the stage itself. -/
noncomputable def pullbackLimitToStage
    {X Y : Scheme.{u}} (p : Y ⟶ X)
    [HasPair (RingedSpace.opensRingedSiteHom p.toShHom)]
    {T : SequentialInverseSystem (RingedSpace.ModuleDerived X.toRingedSpace)}
    {Klim K : RingedSpace.ModuleDerived X.toRingedSpace}
    (P : HomotopyLimit.Presentation T Klim) (n : ℕ)
    (G : Y.Modules) (toLimit : K ⟶ Klim)
    (stage : T.obj (Opposite.op n) ⟶
      (RingedSpace.moduleDerivedPushforward p.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) :
    (RingedSpace.modulePullbackDerived p.toShHom).obj K ⟶
      (DerivedCategory.singleFunctor Y.Modules 0).obj G :=
  ((RingedSpace.modulePullbackDerivedPushforwardAdjunction p.toShHom).homEquiv _ _).symm
    (limitToStagePushforward p P n G toLimit stage)

/-- The adjunct of `pullbackLimitToStage` is the displayed limit-to-stage composite. -/
theorem pullbackLimitToStage_adjunct
    {X Y : Scheme.{u}} (p : Y ⟶ X)
    [HasPair (RingedSpace.opensRingedSiteHom p.toShHom)]
    {T : SequentialInverseSystem (RingedSpace.ModuleDerived X.toRingedSpace)}
    {Klim K : RingedSpace.ModuleDerived X.toRingedSpace}
    (P : HomotopyLimit.Presentation T Klim) (n : ℕ)
    (G : Y.Modules) (toLimit : K ⟶ Klim)
    (stage : T.obj (Opposite.op n) ⟶
      (RingedSpace.moduleDerivedPushforward p.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) :
    (RingedSpace.modulePullbackDerivedPushforwardAdjunction p.toShHom).homEquiv _ _
        (pullbackLimitToStage p P n G toLimit stage) =
      limitToStagePushforward p P n G toLimit stage := sorry

/-- A morphism into derived pushforward induces its canonical affine-base-change
morphism after derived extension of scalars. -/
noncomputable def globalSectionsBaseChangeMap
    (A B : CommRingCat.{u}) (s : A ⟶ B)
    {X Y : Scheme.{u}} (f : X ⟶ Spec A) (q : Y ⟶ Spec B) (p : Y ⟶ X)
    (h_sections :
      s ≫ (Scheme.ΓSpecIso B).inv ≫ q.appTop =
        (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫ p.appTop)
    {L : RingedSpace.ModuleDerived X.toRingedSpace}
    {G : RingedSpace.ModuleDerived Y.toRingedSpace}
    (a : L ⟶ (RingedSpace.moduleDerivedPushforward p.toShHom).obj G) :
    (ModuleCat.derivedExtensionOfScalars s.hom).obj
        ((Scheme.FlatPullbackSections.baseSections f).obj L) ⟶
      (Scheme.FlatPullbackSections.baseSections q).obj G :=
  (ModuleCat.derivedExtensionRestrictionHomEquiv s.hom _ _).symm
    ((ModuleCat.DerivedRestriction.compObjIso
          (Scheme.ΓSpecIso A).inv.hom f.appTop.hom
          ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj L)).inv ≫
      (ModuleCat.derivedRestrictionOfScalars
        (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom)).map
          (RingedSpace.Module.Derived.GlobalSections.mapOfPushforward p.toShHom a) ≫
      (ModuleCat.DerivedRestriction.compObjIso
        (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) p.appTop.hom
        ((RingedSpace.Module.Derived.GlobalSections.functor Y.toRingedSpace).obj G)).inv ≫
      eqToHom (congrArg
        (fun r ↦ (ModuleCat.derivedRestrictionOfScalars r).obj
          ((RingedSpace.Module.Derived.GlobalSections.functor Y.toRingedSpace).obj G))
        (congrArg CommRingCat.Hom.hom h_sections).symm) ≫
      (ModuleCat.DerivedRestriction.compObjIso s.hom
        (((Scheme.ΓSpecIso B).inv ≫ q.appTop).hom)
        ((RingedSpace.Module.Derived.GlobalSections.functor Y.toRingedSpace).obj G)).hom ≫
      (ModuleCat.derivedRestrictionOfScalars s.hom).map
        ((ModuleCat.DerivedRestriction.compObjIso
          (Scheme.ΓSpecIso B).inv.hom q.appTop.hom
          ((RingedSpace.Module.Derived.GlobalSections.functor Y.toRingedSpace).obj G)).hom))

/-- Transposing `globalSectionsBaseChangeMap` recovers the restricted-scalar
change-of-space composite used in its definition. -/
theorem globalSectionsBaseChangeMap_adjunct
    (A B : CommRingCat.{u}) (s : A ⟶ B)
    {X Y : Scheme.{u}} (f : X ⟶ Spec A) (q : Y ⟶ Spec B) (p : Y ⟶ X)
    (h_sections :
      s ≫ (Scheme.ΓSpecIso B).inv ≫ q.appTop =
        (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫ p.appTop)
    {L : RingedSpace.ModuleDerived X.toRingedSpace}
    {G : RingedSpace.ModuleDerived Y.toRingedSpace}
    (a : L ⟶ (RingedSpace.moduleDerivedPushforward p.toShHom).obj G) :
    ModuleCat.derivedExtensionRestrictionHomEquiv s.hom _ _
      (globalSectionsBaseChangeMap A B s f q p h_sections a) =
        (ModuleCat.DerivedRestriction.compObjIso
            (Scheme.ΓSpecIso A).inv.hom f.appTop.hom
            ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj L)).inv ≫
          (ModuleCat.derivedRestrictionOfScalars
            (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom)).map
              (RingedSpace.Module.Derived.GlobalSections.mapOfPushforward p.toShHom a) ≫
          (ModuleCat.DerivedRestriction.compObjIso
            (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) p.appTop.hom
            ((RingedSpace.Module.Derived.GlobalSections.functor Y.toRingedSpace).obj G)).inv ≫
          eqToHom (congrArg
            (fun r ↦ (ModuleCat.derivedRestrictionOfScalars r).obj
              ((RingedSpace.Module.Derived.GlobalSections.functor Y.toRingedSpace).obj G))
            (congrArg CommRingCat.Hom.hom h_sections).symm) ≫
          (ModuleCat.DerivedRestriction.compObjIso s.hom
            (((Scheme.ΓSpecIso B).inv ≫ q.appTop).hom)
            ((RingedSpace.Module.Derived.GlobalSections.functor Y.toRingedSpace).obj G)).hom ≫
          (ModuleCat.derivedRestrictionOfScalars s.hom).map
            ((ModuleCat.DerivedRestriction.compObjIso
              (Scheme.ΓSpecIso B).inv.hom q.appTop.hom
              ((RingedSpace.Module.Derived.GlobalSections.functor Y.toRingedSpace).obj G)).hom) := sorry

/-- The canonical tensor comparison obtained from a presented limit-to-stage map and
the affine change-of-space construction. -/
noncomputable def globalSectionsTensorBaseChangeMapOfStage
    (A B : CommRingCat.{u}) (s : A ⟶ B)
    {X Y : Scheme.{u}} (f : X ⟶ Spec A) (q : Y ⟶ Spec B) (p : Y ⟶ X)
    (h_sections :
      s ≫ (Scheme.ΓSpecIso B).inv ≫ q.appTop =
        (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫ p.appTop)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom p.toShHom)]
    [(RingedSpace.modulePullbackDerived p.toShHom).Monoidal]
    (T_X : @DerivedTensor.Right.Monoidal.Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_Y : @DerivedTensor.Right.Monoidal.Model
      (RingedSpace.Modules Y.toRingedSpace) _ _ _ _ _ _ _)
    {T : SequentialInverseSystem (RingedSpace.ModuleDerived X.toRingedSpace)}
    {Klim K : RingedSpace.ModuleDerived X.toRingedSpace}
    (P : HomotopyLimit.Presentation T Klim) (n : ℕ)
    (G : Y.Modules) (toLimit : K ⟶ Klim)
    (stage : T.obj (Opposite.op n) ⟶
      (RingedSpace.moduleDerivedPushforward p.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G))
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    (ModuleCat.derivedExtensionOfScalars s.hom).obj
        ((Scheme.FlatPullbackSections.baseSections f).obj
          (@DerivedTensor.Right.obj X.Modules _ _ _ _ _ _ K E
            (Scheme.Modules.hasDerivedTensorRight X))) ⟶
      (Scheme.FlatPullbackSections.baseSections q).obj
        (@DerivedTensor.Right.obj Y.Modules _ _ _ _ _ _
          ((DerivedCategory.singleFunctor Y.Modules 0).obj G)
          ((RingedSpace.modulePullbackDerived p.toShHom).obj E)
          (Scheme.Modules.hasDerivedTensorRight Y)) :=
  globalSectionsBaseChangeMap A B s f q p h_sections
    ((RingedSpace.modulePullbackDerivedPushforwardAdjunction p.toShHom).homEquiv _ _
      ((RingedSpace.modulePullbackDerived p.toShHom).map
          (T_X.objIsoTensor K E).hom ≫
        (Functor.Monoidal.μIso
          (RingedSpace.modulePullbackDerived p.toShHom) K E).symm.hom ≫
        (pullbackLimitToStage p P n G toLimit stage ⊗ₘ
          𝟙 ((RingedSpace.modulePullbackDerived p.toShHom).obj E)) ≫
        (T_Y.objIsoTensor
          ((DerivedCategory.singleFunctor Y.Modules 0).obj G)
          ((RingedSpace.modulePullbackDerived p.toShHom).obj E)).inv))

/-- The tensor limit comparison is the affine change-of-space map induced by the
monoidal pullback of the limit-to-stage comparison. -/
theorem globalSectionsTensorBaseChangeMapOfStage_def
    (A B : CommRingCat.{u}) (s : A ⟶ B)
    {X Y : Scheme.{u}} (f : X ⟶ Spec A) (q : Y ⟶ Spec B) (p : Y ⟶ X)
    (h_sections :
      s ≫ (Scheme.ΓSpecIso B).inv ≫ q.appTop =
        (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫ p.appTop)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom p.toShHom)]
    [(RingedSpace.modulePullbackDerived p.toShHom).Monoidal]
    (T_X : @DerivedTensor.Right.Monoidal.Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_Y : @DerivedTensor.Right.Monoidal.Model
      (RingedSpace.Modules Y.toRingedSpace) _ _ _ _ _ _ _)
    {T : SequentialInverseSystem (RingedSpace.ModuleDerived X.toRingedSpace)}
    {Klim K : RingedSpace.ModuleDerived X.toRingedSpace}
    (P : HomotopyLimit.Presentation T Klim) (n : ℕ)
    (G : Y.Modules) (toLimit : K ⟶ Klim)
    (stage : T.obj (Opposite.op n) ⟶
      (RingedSpace.moduleDerivedPushforward p.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G))
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    globalSectionsTensorBaseChangeMapOfStage A B s f q p h_sections
        T_X T_Y P n G toLimit stage E =
      globalSectionsBaseChangeMap A B s f q p h_sections
        ((RingedSpace.modulePullbackDerivedPushforwardAdjunction p.toShHom).homEquiv _ _
          ((RingedSpace.modulePullbackDerived p.toShHom).map
              (T_X.objIsoTensor K E).hom ≫
            (Functor.Monoidal.μIso
              (RingedSpace.modulePullbackDerived p.toShHom) K E).symm.hom ≫
            (pullbackLimitToStage p P n G toLimit stage ⊗ₘ
              𝟙 ((RingedSpace.modulePullbackDerived p.toShHom).obj E)) ≫
            (T_Y.objIsoTensor
              ((DerivedCategory.singleFunctor Y.Modules 0).obj G)
              ((RingedSpace.modulePullbackDerived p.toShHom).obj E)).inv)) := sorry

/-- The canonical internal-Hom comparison obtained from a presented limit-to-stage map
and the affine change-of-space construction. -/
noncomputable def globalHomBaseChangeMapOfStage
    (A B : CommRingCat.{u}) (s : A ⟶ B)
    {X Y : Scheme.{u}} (f : X ⟶ Spec A) (q : Y ⟶ Spec B) (p : Y ⟶ X)
    (h_sections :
      s ≫ (Scheme.ΓSpecIso B).inv ≫ q.appTop =
        (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫ p.appTop)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom p.toShHom)]
    [(RingedSpace.modulePullbackDerived p.toShHom).Monoidal]
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_Y : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    {T : SequentialInverseSystem (RingedSpace.ModuleDerived X.toRingedSpace)}
    {Klim K : RingedSpace.ModuleDerived X.toRingedSpace}
    (P : HomotopyLimit.Presentation T Klim) (n : ℕ)
    (G : Y.Modules) (toLimit : K ⟶ Klim)
    (stage : T.obj (Opposite.op n) ⟶
      (RingedSpace.moduleDerivedPushforward p.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G))
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    (ModuleCat.derivedExtensionOfScalars s.hom).obj
        ((Scheme.FlatPullbackSections.baseSections f).obj ((H_X.ihomOf E).obj K)) ⟶
      (Scheme.FlatPullbackSections.baseSections q).obj
        ((H_Y.ihomOf ((RingedSpace.modulePullbackDerived p.toShHom).obj E)).obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) :=
  globalSectionsBaseChangeMap A B s f q p h_sections
    ((H_X.ihomOf E).map (limitToStagePushforward p P n G toLimit stage) ≫
      (CategoryTheory.Adjunction.InternalHom.comparisonIso
        (RingedSpace.modulePullbackDerivedPushforwardAdjunction p.toShHom)
        H_X H_Y
        (Functor.TensorComparison.ofMonoidal
          (RingedSpace.modulePullbackDerived p.toShHom)) E
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G)).hom)

/-- The internal-Hom limit comparison is the affine change-of-space map induced by
covariance and the pullback-pushforward internal-Hom comparison. -/
theorem globalHomBaseChangeMapOfStage_def
    (A B : CommRingCat.{u}) (s : A ⟶ B)
    {X Y : Scheme.{u}} (f : X ⟶ Spec A) (q : Y ⟶ Spec B) (p : Y ⟶ X)
    (h_sections :
      s ≫ (Scheme.ΓSpecIso B).inv ≫ q.appTop =
        (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫ p.appTop)
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom p.toShHom)]
    [(RingedSpace.modulePullbackDerived p.toShHom).Monoidal]
    (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (H_Y : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    {T : SequentialInverseSystem (RingedSpace.ModuleDerived X.toRingedSpace)}
    {Klim K : RingedSpace.ModuleDerived X.toRingedSpace}
    (P : HomotopyLimit.Presentation T Klim) (n : ℕ)
    (G : Y.Modules) (toLimit : K ⟶ Klim)
    (stage : T.obj (Opposite.op n) ⟶
      (RingedSpace.moduleDerivedPushforward p.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G))
    (E : RingedSpace.ModuleDerived X.toRingedSpace) :
    globalHomBaseChangeMapOfStage A B s f q p h_sections H_X H_Y
        P n G toLimit stage E =
      globalSectionsBaseChangeMap A B s f q p h_sections
        ((H_X.ihomOf E).map (limitToStagePushforward p P n G toLimit stage) ≫
          (CategoryTheory.Adjunction.InternalHom.comparisonIso
            (RingedSpace.modulePullbackDerivedPushforwardAdjunction p.toShHom)
            H_X H_Y
            (Functor.TensorComparison.ofMonoidal
              (RingedSpace.modulePullbackDerived p.toShHom)) E
            ((DerivedCategory.singleFunctor Y.Modules 0).obj G)).hom) := sorry

/-- The canonical tensor base-change map from a presented homotopy limit to a stage of a
cartesian system of closed thickenings. -/
noncomputable def globalSectionsTensorLimitBaseChangeMap
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (X : Scheme.{u}) (f : X ⟶ Spec A_lim.cone.pt)
    [IsSeparated f] [Scheme.Hom.FinitePresentation f]
    (Xn : ℕ → Scheme.{u}) (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n)))
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f)
    [∀ n, IsClosedImmersion (p n)]
    (ℱ : ∀ n, (Xn n).Modules) [∀ n, (ℱ n).IsFinitePresentation]
    (F : SequentialInverseSystem (Scheme.QCoh X))
    (stageIso : ∀ n, F.obj (Opposite.op n) ≅
      (Scheme.QCoh.pushforward (p n)).obj
        (⟨ℱ n, inferInstance⟩ : Scheme.QCoh (Xn n)))
    (Klim : RingedSpace.ModuleDerived X.toRingedSpace)
    (P : HomotopyLimit.Presentation
      (F ⋙ Scheme.QCoh.inclusion X ⋙
        DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) Klim)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [∀ n, HomotopyTensorDescends (Xn n).toRingedSpace]
    [∀ n, TensorDescends (Xn n).toRingedSpace]
    [∀ n, IsLocalization (Xn n).toRingedSpace]
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (p n).toShHom)]
    [∀ n, (RingedSpace.modulePullbackDerived (p n).toShHom).Monoidal]
    (T_X : @Monoidal.Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_Xn : ∀ n, @Monoidal.Model
      (RingedSpace.Modules (Xn n).toRingedSpace) _ _ _ _ _ _ _)
    (n : ℕ) :=
  globalSectionsTensorBaseChangeMapOfStage
    A_lim.cone.pt (A.obj (Opposite.op n)) (A_lim.cone.stageMap n)
    f (q n) (p n)
    ((Scheme.ΓSpecIso_inv_naturality_assoc
        (A_lim.cone.stageMap n) (q n).appTop).trans
      (congrArg (fun k ↦ (Scheme.ΓSpecIso A_lim.cone.pt).inv ≫ k)
        (congrArg (fun k : Xn n ⟶ Spec A_lim.cone.pt ↦ k.appTop)
          (h_pullback n).w)))
    T_X (T_Xn n) P n (ℱ n)
    ((@Adjunction.ofIsLeftAdjoint _ _ _ _
      (ModuleDerived.Quasicoherent.inclusion X)
      (@inclusionIsLeftAdjoint X
        (Scheme.Hom.compactSpace_of_finitePresentation f)
        (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).counit.app Klim)
    (thickeningSystemStageMap (p n) F (ℱ n) n (stageIso n)) E

/-- `globalSectionsTensorLimitBaseChangeMap` is the stagewise tensor comparison
induced by the chosen homotopy-limit presentation. -/
theorem globalSectionsTensorLimitBaseChangeMap_def
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (X : Scheme.{u}) (f : X ⟶ Spec A_lim.cone.pt)
    [IsSeparated f] [Scheme.Hom.FinitePresentation f]
    (Xn : ℕ → Scheme.{u}) (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n)))
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f)
    [∀ n, IsClosedImmersion (p n)]
    (ℱ : ∀ n, (Xn n).Modules) [∀ n, (ℱ n).IsFinitePresentation]
    (F : SequentialInverseSystem (Scheme.QCoh X))
    (stageIso : ∀ n, F.obj (Opposite.op n) ≅
      (Scheme.QCoh.pushforward (p n)).obj
        (⟨ℱ n, inferInstance⟩ : Scheme.QCoh (Xn n)))
    (Klim : RingedSpace.ModuleDerived X.toRingedSpace)
    (P : HomotopyLimit.Presentation
      (F ⋙ Scheme.QCoh.inclusion X ⋙
        DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) Klim)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [∀ n, HomotopyTensorDescends (Xn n).toRingedSpace]
    [∀ n, TensorDescends (Xn n).toRingedSpace]
    [∀ n, IsLocalization (Xn n).toRingedSpace]
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (p n).toShHom)]
    [∀ n, (RingedSpace.modulePullbackDerived (p n).toShHom).Monoidal]
    (T_X : @Monoidal.Model
      (RingedSpace.Modules X.toRingedSpace) _ _ _ _ _ _ _)
    (T_Xn : ∀ n, @Monoidal.Model
      (RingedSpace.Modules (Xn n).toRingedSpace) _ _ _ _ _ _ _)
    (n : ℕ) :
    globalSectionsTensorLimitBaseChangeMap A A_lim X f Xn p q h_pullback
        ℱ F stageIso Klim P E T_X T_Xn n =
      globalSectionsTensorBaseChangeMapOfStage
        A_lim.cone.pt (A.obj (Opposite.op n)) (A_lim.cone.stageMap n)
        f (q n) (p n)
        ((Scheme.ΓSpecIso_inv_naturality_assoc
            (A_lim.cone.stageMap n) (q n).appTop).trans
          (congrArg (fun k ↦ (Scheme.ΓSpecIso A_lim.cone.pt).inv ≫ k)
            (congrArg (fun k : Xn n ⟶ Spec A_lim.cone.pt ↦ k.appTop)
              (h_pullback n).w)))
        T_X (T_Xn n) P n (ℱ n)
        ((@Adjunction.ofIsLeftAdjoint _ _ _ _
          (ModuleDerived.Quasicoherent.inclusion X)
          (@inclusionIsLeftAdjoint X
            (Scheme.Hom.compactSpace_of_finitePresentation f)
            (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).counit.app Klim)
        (thickeningSystemStageMap (p n) F (ℱ n) n (stageIso n)) E := sorry

/-- The canonical internal-Hom base-change map from a presented homotopy limit to a stage
of a cartesian system of closed thickenings. -/
noncomputable def globalHomLimitBaseChangeMap
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (X : Scheme.{u}) (f : X ⟶ Spec A_lim.cone.pt)
    [IsSeparated f] [Scheme.Hom.FinitePresentation f]
    (Xn : ℕ → Scheme.{u}) (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n)))
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f)
    [∀ n, IsClosedImmersion (p n)]
    (ℱ : ∀ n, (Xn n).Modules) [∀ n, (ℱ n).IsFinitePresentation]
    (F : SequentialInverseSystem (Scheme.QCoh X))
    (stageIso : ∀ n, F.obj (Opposite.op n) ≅
      (Scheme.QCoh.pushforward (p n)).obj
        (⟨ℱ n, inferInstance⟩ : Scheme.QCoh (Xn n)))
    (Klim : RingedSpace.ModuleDerived X.toRingedSpace)
    (P : HomotopyLimit.Presentation
      (F ⋙ Scheme.QCoh.inclusion X ⋙
        DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) Klim)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [∀ n, HomotopyTensorDescends (Xn n).toRingedSpace]
    [∀ n, TensorDescends (Xn n).toRingedSpace]
    [∀ n, IsLocalization (Xn n).toRingedSpace]
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (p n).toShHom)]
    [∀ n, (RingedSpace.modulePullbackDerived (p n).toShHom).Monoidal]
    (H_X : @MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace) _
      (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace))
    (H_Xn : ∀ n, @MonoidalClosed
      (RingedSpace.ModuleDerived (Xn n).toRingedSpace) _
      (RingedSpace.ModuleDerived.monoidalCategory (Xn n).toRingedSpace))
    (n : ℕ) :=
  globalHomBaseChangeMapOfStage
    A_lim.cone.pt (A.obj (Opposite.op n)) (A_lim.cone.stageMap n)
    f (q n) (p n)
    ((Scheme.ΓSpecIso_inv_naturality_assoc
        (A_lim.cone.stageMap n) (q n).appTop).trans
      (congrArg (fun k ↦ (Scheme.ΓSpecIso A_lim.cone.pt).inv ≫ k)
        (congrArg (fun k : Xn n ⟶ Spec A_lim.cone.pt ↦ k.appTop)
          (h_pullback n).w)))
    H_X (H_Xn n) P n (ℱ n)
    ((@Adjunction.ofIsLeftAdjoint _ _ _ _
      (ModuleDerived.Quasicoherent.inclusion X)
      (@inclusionIsLeftAdjoint X
        (Scheme.Hom.compactSpace_of_finitePresentation f)
        (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).counit.app Klim)
    (thickeningSystemStageMap (p n) F (ℱ n) n (stageIso n)) E

/-- `globalHomLimitBaseChangeMap` is the stagewise internal-Hom comparison induced
by the chosen homotopy-limit presentation. -/
theorem globalHomLimitBaseChangeMap_def
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (X : Scheme.{u}) (f : X ⟶ Spec A_lim.cone.pt)
    [IsSeparated f] [Scheme.Hom.FinitePresentation f]
    (Xn : ℕ → Scheme.{u}) (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n)))
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f)
    [∀ n, IsClosedImmersion (p n)]
    (ℱ : ∀ n, (Xn n).Modules) [∀ n, (ℱ n).IsFinitePresentation]
    (F : SequentialInverseSystem (Scheme.QCoh X))
    (stageIso : ∀ n, F.obj (Opposite.op n) ≅
      (Scheme.QCoh.pushforward (p n)).obj
        (⟨ℱ n, inferInstance⟩ : Scheme.QCoh (Xn n)))
    (Klim : RingedSpace.ModuleDerived X.toRingedSpace)
    (P : HomotopyLimit.Presentation
      (F ⋙ Scheme.QCoh.inclusion X ⋙
        DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)) Klim)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [∀ n, HomotopyTensorDescends (Xn n).toRingedSpace]
    [∀ n, TensorDescends (Xn n).toRingedSpace]
    [∀ n, IsLocalization (Xn n).toRingedSpace]
    [∀ n, HasPair (RingedSpace.opensRingedSiteHom (p n).toShHom)]
    [∀ n, (RingedSpace.modulePullbackDerived (p n).toShHom).Monoidal]
    (H_X : @MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace) _
      (RingedSpace.ModuleDerived.monoidalCategory X.toRingedSpace))
    (H_Xn : ∀ n, @MonoidalClosed
      (RingedSpace.ModuleDerived (Xn n).toRingedSpace) _
      (RingedSpace.ModuleDerived.monoidalCategory (Xn n).toRingedSpace))
    (n : ℕ) :
    globalHomLimitBaseChangeMap A A_lim X f Xn p q h_pullback
        ℱ F stageIso Klim P E H_X H_Xn n =
      globalHomBaseChangeMapOfStage
        A_lim.cone.pt (A.obj (Opposite.op n)) (A_lim.cone.stageMap n)
        f (q n) (p n)
        ((Scheme.ΓSpecIso_inv_naturality_assoc
            (A_lim.cone.stageMap n) (q n).appTop).trans
          (congrArg (fun k ↦ (Scheme.ΓSpecIso A_lim.cone.pt).inv ≫ k)
            (congrArg (fun k : Xn n ⟶ Spec A_lim.cone.pt ↦ k.appTop)
              (h_pullback n).w)))
        H_X (H_Xn n) P n (ℱ n)
        ((@Adjunction.ofIsLeftAdjoint _ _ _ _
          (ModuleDerived.Quasicoherent.inclusion X)
          (@inclusionIsLeftAdjoint X
            (Scheme.Hom.compactSpace_of_finitePresentation f)
            (Scheme.Hom.quasiSeparatedSpace_of_finitePresentation f))).counit.app Klim)
        (thickeningSystemStageMap (p n) F (ℱ n) n (stageIso n)) E := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
