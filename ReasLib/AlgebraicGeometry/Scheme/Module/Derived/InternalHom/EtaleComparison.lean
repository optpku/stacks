/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.EtaleComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift.Exact
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.ZariskiComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InternalHom.Bifunctor
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.Derived.Over
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom.Complex

/-!
# Étale affine comparison for derived internal Hom

This file constructs the composite `ε^* ∘ tilde` from `D(A)` to `D(𝒪_étale)` on
`Spec(A)` and the canonical comparison from `ε^*` of affine `RHom` to the derived
internal Hom of the pulled-back complexes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.InternalHom
open CategoryTheory.MonoidalClosed
open Functor.PullbackInternalHom.Left
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.Scheme.AssociatedModule
open CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open Opposite

open scoped DifferentialGradedCategory CategoryTheory.CochainComplex.Enriched.Over

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.InternalHom

/-- The exact derived functor `ε^* ∘ tilde` from `D(A)` to derived modules on the
small étale site of `Spec(A)`. -/
noncomputable abbrev affineEtaleTildeDerived (A : Type u) [CommRing A] :
    DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory
        (SheafOfModules.{u}
          (Scheme.Etale.Small.structureSheaf (Spec (CommRingCat.of A)))) :=
  affineTildeDerived A ⋙
    schemeToZariskiDerived (Spec (CommRingCat.of A)) ⋙
      (epsilonModulePullback (Spec (CommRingCat.of A))).mapDerivedCategory

/-- `affineEtaleTildeDerived` is the composite of affine tilde, the Zariski comparison,
and exact pullback along `smallEtaleToZariski`. -/
theorem affineEtaleTildeDerived_eq (A : Type u) [CommRing A] :
    affineEtaleTildeDerived A =
      affineTildeDerived A ⋙
        schemeToZariskiDerived (Spec (CommRingCat.of A)) ⋙
          (epsilonModulePullback (Spec (CommRingCat.of A))).mapDerivedCategory :=
  rfl

/-- Objectwise, `affineEtaleTildeDerived` applies affine tilde, then the Zariski
comparison, then exact étale pullback. -/
theorem affineEtaleTildeDerived_obj (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (affineEtaleTildeDerived A).obj K =
      ((epsilonModulePullback (Spec (CommRingCat.of A))).mapDerivedCategory).obj
        ((schemeToZariskiDerived (Spec (CommRingCat.of A))).obj
          ((affineTildeDerived A).obj K)) :=
  rfl

/-- Affine tilde, Zariski pushforward, étale pullback, coefficient transport,
and universe lifting, composed as exact functors. -/
def affineEtaleModuleExact (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ₑ RingedSite.ModuleCat.{u + 1}
      (smallCommRingedSite .etale (Spec (CommRingCat.of A))) :=
  ExactFunctor.comp
    (ExactFunctor.comp
      (ExactFunctor.comp
        (⟨tilde.functor (CommRingCat.of A), tilde.exact (CommRingCat.of A)⟩ :
          ModuleCat.{u} A ⥤ₑ (Spec (CommRingCat.of A)).Modules)
        (zariskiModulePushforward (Spec (CommRingCat.of A))))
      (epsilonModulePullback (Spec (CommRingCat.of A))))
    (etaleModuleLiftExact (Spec (CommRingCat.of A)))

/-- The ordinary module-sheaf functor underlying the exact affine étale
associated-module construction. -/
abbrev affineEtaleModuleFunctor (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ RingedSite.ModuleCat.{u + 1}
      (smallCommRingedSite .etale (Spec (CommRingCat.of A))) :=
  (affineEtaleModuleExact A).obj

/-- The lifted affine étale module is canonically its associated-module
presentation on the standard small étale site. -/
def affineEtaleModulePresentationIso {A : Type u} [CommRing A]
    (M : ModuleCat.{u} A) :
    (affineEtaleModuleFunctor A).obj M ≅
      StandardSmall.comm .etale (Spec (CommRingCat.of A)) (tilde M) :=
  (smallModuleLift (Spec (CommRingCat.of A)) .etale).mapIso
    (etalePresentationIso (Spec (CommRingCat.of A)) ⟨tilde M, inferInstance⟩) ≪≫
      smallModuleLiftIso (Spec (CommRingCat.of A)) .etale ⟨tilde M, inferInstance⟩

/-- The affine étale derived functor with coefficients and modules lifted to
the commutative small-site presentation. -/
@[implicit_reducible]
def affineEtaleTildeDerivedLift (A : Type u) [CommRing A] :
    DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (RingedSite.ModuleCat.{u + 1}
        (smallCommRingedSite .etale (Spec (CommRingCat.of A)))) :=
  affineEtaleTildeDerived A ⋙
    (etaleModuleLiftExact (Spec (CommRingCat.of A))).mapDerivedCategory

/-- Deriving the exact affine étale composite agrees with composing the
derived affine, Zariski, étale, and coefficient-lift functors. -/
def affineEtaleModuleDerivedIso (A : Type u) [CommRing A] :
    (affineEtaleModuleExact A).mapDerivedCategory ≅ affineEtaleTildeDerivedLift A := by
  let X := Spec (CommRingCat.of A)
  let T : ModuleCat.{u} A ⥤ₑ X.Modules :=
    ⟨tilde.functor (CommRingCat.of A), tilde.exact (CommRingCat.of A)⟩
  let Z := zariskiModulePushforward X
  let E := epsilonModulePullback X
  let V := etaleModuleLiftExact X
  let z : Z.mapDerivedCategory ≅ schemeToZariskiDerived X :=
    ExactFunctor.MapDerivedCategory.compFunctorIso
        (opensToSmallZariskiModulePushforward X)
        (smallZariskiToZariskiSmallModulePushforward X) ≪≫
      (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight
        (ExactFunctor.MapDerivedCategory.idFunctorIso X.Modules).symm _
  let tz : (T.comp Z).mapDerivedCategory ≅
      affineTildeDerived A ⋙ schemeToZariskiDerived X :=
    ExactFunctor.MapDerivedCategory.compFunctorIso T Z ≪≫
      Functor.isoWhiskerLeft T.mapDerivedCategory z
  let tze : ((T.comp Z).comp E).mapDerivedCategory ≅ affineEtaleTildeDerived A :=
    ExactFunctor.MapDerivedCategory.compFunctorIso (T.comp Z) E ≪≫
      Functor.isoWhiskerRight tz E.mapDerivedCategory ≪≫
      Functor.associator _ _ _
  exact ExactFunctor.MapDerivedCategory.compFunctorIso ((T.comp Z).comp E) V ≪≫
    Functor.isoWhiskerRight tze V.mapDerivedCategory

/-- The derived-composition isomorphism agrees with the cochain localization
factor and the iterated exact-derived composition factors. -/
theorem affineEtaleModuleDerivedIso_fac (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
  let X := Spec (CommRingCat.of A)
  let T : ModuleCat.{u} A ⥤ₑ X.Modules :=
    ⟨tilde.functor (CommRingCat.of A), tilde.exact (CommRingCat.of A)⟩
  let Z := zariskiModulePushforward X
  let E := epsilonModulePullback X
  let V := etaleModuleLiftExact X
  let z : Z.mapDerivedCategory ≅ schemeToZariskiDerived X :=
    ExactFunctor.MapDerivedCategory.compFunctorIso
        (opensToSmallZariskiModulePushforward X)
        (smallZariskiToZariskiSmallModulePushforward X) ≪≫
      (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight
        (ExactFunctor.MapDerivedCategory.idFunctorIso X.Modules).symm _
  let tz : (T.comp Z).mapDerivedCategory ≅
      affineTildeDerived A ⋙ schemeToZariskiDerived X :=
    ExactFunctor.MapDerivedCategory.compFunctorIso T Z ≪≫
      Functor.isoWhiskerLeft T.mapDerivedCategory z
  let tze : ((T.comp Z).comp E).mapDerivedCategory ≅ affineEtaleTildeDerived A :=
    ExactFunctor.MapDerivedCategory.compFunctorIso (T.comp Z) E ≪≫
      Functor.isoWhiskerRight tz E.mapDerivedCategory ≪≫
      Functor.associator _ _ _
  (affineEtaleModuleDerivedIso A).hom.app (DerivedCategory.Q.obj M) =
    (affineEtaleModuleExact A).obj.mapDerivedCategoryFactors.hom.app M ≫
      (ExactFunctor.MapDerivedCategory.compFactors ((T.comp Z).comp E) V).inv.app M ≫
      V.mapDerivedCategory.map (tze.hom.app (DerivedCategory.Q.obj M)) := sorry

/-- Affine étale tensor comparison, obtained from associated-module tensor
products and the affine tilde tensor comparison. -/
def affineEtaleTensorComparison {A : Type u} [CommRing A]
    (M N : ModuleCat.{u} A) :
    (affineEtaleModuleFunctor A).obj M ⊗ (affineEtaleModuleFunctor A).obj N ⟶
      (affineEtaleModuleFunctor A).obj (M ⊗ N) := by
  let X := Spec (CommRingCat.of A)
  let F : Scheme.QCoh X := ⟨tilde M, inferInstance⟩
  let G : Scheme.QCoh X := ⟨tilde N, inferInstance⟩
  let P := quasicoherentTensor X F G
  let T : Scheme.QCoh X := ⟨tilde (M ⊗ N), inferInstance⟩
  let f : P ⟶ T :=
    ⟨tilde.Tensor.comparisonInv (R := CommRingCat.of A) M N
      (tilde.Tensor.comparisonIsIso (R := CommRingCat.of A) M N)⟩
  let a : (affineEtaleModuleFunctor A).obj M ⊗
      (affineEtaleModuleFunctor A).obj N ⟶
      StandardSmall.comm .etale X F.obj ⊗ StandardSmall.comm .etale X G.obj :=
    (affineEtaleModulePresentationIso M).hom ⊗ₘ
      (affineEtaleModulePresentationIso N).hom
  let b : StandardSmall.comm .etale X F.obj ⊗ StandardSmall.comm .etale X G.obj ⟶
      StandardSmall.comm .etale X P.obj := smallTensorComparison X .etale F G
  let c : StandardSmall.comm .etale X P.obj ⟶ StandardSmall.comm .etale X T.obj :=
    (smallModuleLiftIso X .etale P).inv ≫
      (smallModuleLift X .etale).map ((smallModuleFunctor X .etale).map f) ≫
      (smallModuleLiftIso X .etale T).hom
  let d : StandardSmall.comm .etale X T.obj ⟶
      (affineEtaleModuleFunctor A).obj (M ⊗ N) :=
    (affineEtaleModulePresentationIso (M ⊗ N)).inv
  exact a ≫ b ≫ c ≫ d

/-- The affine étale tensor comparison commutes with maps in both modules. -/
theorem affineEtaleTensorComparison_naturality {A : Type u} [CommRing A]
    {M M' N N' : ModuleCat.{u} A} (f : M ⟶ M') (g : N ⟶ N') :
    ((affineEtaleModuleFunctor A).map f ⊗ₘ (affineEtaleModuleFunctor A).map g) ≫
        affineEtaleTensorComparison M' N' =
      affineEtaleTensorComparison M N ≫ (affineEtaleModuleFunctor A).map (f ⊗ₘ g) :=
  sorry

/-- Ordinary module evaluation induces the affine étale internal-Hom
comparison, without a finite-presentation condition on either module. -/
def etaleAffineHomComparison {A : Type u} [CommRing A]
    (M N : ModuleCat.{u} A) :
    (affineEtaleModuleFunctor A).obj (ModuleCat.of A (M ⟶ N)) ⟶
      (ihom ((affineEtaleModuleFunctor A).obj M)).obj
        ((affineEtaleModuleFunctor A).obj N) :=
  CategoryTheory.MonoidalClosed.curry
    (affineEtaleTensorComparison M (ModuleCat.of A (M ⟶ N)) ≫
      (affineEtaleModuleFunctor A).map ((ihom.ev M).app N))

/-- Evaluation comparison is contravariantly natural in the source module
and covariantly natural in the target module. -/
theorem etaleAffineHomComparison_naturality {A : Type u} [CommRing A]
    {M M' N N' : ModuleCat.{u} A} (f : M' ⟶ M) (g : N ⟶ N') :
    (affineEtaleModuleFunctor A).map
        ((MonoidalClosed.pre f).app N ≫ (ihom M').map g) ≫
      etaleAffineHomComparison M' N' =
    etaleAffineHomComparison M N ≫
      (MonoidalClosed.pre ((affineEtaleModuleFunctor A).map f)).app
        ((affineEtaleModuleFunctor A).obj N) ≫
      (ihom ((affineEtaleModuleFunctor A).obj M')).map
        ((affineEtaleModuleFunctor A).map g) := sorry

set_option backward.privateInPublic true in
private def etaleAffineComparisonDegree {A : Type u} [CommRing A]
    (M N : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (affineEtaleModuleFunctor A).obj
        ((CochainComplex.Enriched.Over.homComplex (R := A) M N).X n) ⟶
      (((RingedSite.Hom.ModuleDerived.InternalHom.strictInternalHom
        (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
        (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))).obj
        (op (((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).obj M))).obj
          (((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).obj N)).X n :=
  Pi.lift fun i ↦
    (affineEtaleModuleFunctor A).map (CochainComplex.HomComplex.proj A M N n i) ≫
      etaleAffineHomComparison (M.X i) (N.X (i + n))

set_option backward.privateInPublic true in
private theorem etaleAffineComparisonComplex_comm {A : Type u} [CommRing A]
    (M N : CochainComplex (ModuleCat.{u} A) ℤ) (n m : ℤ) :
    (((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.Enriched.Over.homComplex (R := A) M N)).d n m ≫
      etaleAffineComparisonDegree M N m =
    etaleAffineComparisonDegree M N n ≫
      (((RingedSite.Hom.ModuleDerived.InternalHom.strictInternalHom
        (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
        (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))).obj
        (op (((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).obj M))).obj
          (((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).obj N)).d n m :=
  sorry

-- Local declaration justification (metaprogramming implementation): the public
-- cochain map packages private degree maps and their differential law.
set_option backward.privateInPublic true in
/-- The product of mapped module-Hom projections followed by evaluation
comparison gives a map to the strict sheaf internal-Hom complex. -/
def etaleAffineComparisonComplex {A : Type u} [CommRing A]
    (M N : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.Enriched.Over.homComplex (R := A) M N) ⟶
      ((RingedSite.Hom.ModuleDerived.InternalHom.strictInternalHom
        (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
        (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))).obj
        (op (((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).obj M))).obj
          (((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).obj N) where
  f := etaleAffineComparisonDegree M N
  comm' n m _ := (etaleAffineComparisonComplex_comm M N n m).symm

/-- The cochain evaluation comparison commutes with actual cochain
precomposition and postcomposition. -/
theorem etaleAffineComparisonComplex_naturality {A : Type u} [CommRing A]
    {M M' N N' : CochainComplex (ModuleCat.{u} A) ℤ}
    (f : M' ⟶ M) (g : N ⟶ N') :
    ((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.Enriched.Over.homComplexMap (R := A) f g) ≫
      etaleAffineComparisonComplex M' N' =
    etaleAffineComparisonComplex M N ≫
      ((RingedSite.Hom.ModuleDerived.InternalHom.strictInternalHom
        (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
        (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))).map
        (((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).map f).op).app
          (((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).obj N) ≫
      ((RingedSite.Hom.ModuleDerived.InternalHom.strictInternalHom
        (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
        (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))).obj
        (op (((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).obj M'))).map
          (((affineEtaleModuleFunctor A).mapHomologicalComplex (.up ℤ)).map g) := sorry

/-- The canonical comparison from the lifted affine étale image of module
RHom to the actual sheaf-valued derived internal Hom. -/
def etaleAffineComparison {A : Type u} [CommRing A] [RHom.Has (A := A)]
    (K L : DerivedCategory (ModuleCat.{u} A)) :
    (affineEtaleTildeDerivedLift A).obj (RHom.obj K L) ⟶
      RingedSite.Hom.ModuleDerived.InternalHom.obj
        (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
        (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
        ((affineEtaleTildeDerivedLift A).obj K)
        ((affineEtaleTildeDerivedLift A).obj L) := by
  let C := RingedSite.ModuleCat.{u + 1}
    (smallCommRingedSite .etale (Spec (CommRingCat.of A)))
  let Q : CochainComplex (ModuleCat.{u} A) ℤ ⥤ DerivedCategory (ModuleCat.{u} A) :=
    DerivedCategory.Q
  let S : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let F := affineEtaleModuleFunctor A
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let D := affineEtaleTildeDerivedLift A
  let M := Q.objPreimage K
  let eM : Q.obj M ≅ K := Q.objObjPreimageIso K
  let loc := CochainComplex.Enriched.Over.KInjective.localization
    (R := A) (C := ModuleCat.{u} A)
  let I := @Functor.objPreimage _ _ _ _ loc
    (Localization.essSurj loc
      (CochainComplex.Enriched.Over.KInjective.qis (R := A) (C := ModuleCat.{u} A))) L
  let eI : Q.obj I.obj.obj ≅ L :=
    (CochainComplex.Enriched.Over.derivedQObjIso (R := A)
      (A := ModuleCat.{u} A) I.obj.obj).symm ≪≫
      @Functor.objObjPreimageIso _ _ _ _ loc
        (Localization.essSurj loc
          (CochainComplex.Enriched.Over.KInjective.qis (R := A) (C := ModuleCat.{u} A))) L
  let eH : Q.obj (CochainComplex.Enriched.Over.homComplex (R := A) M I.obj.obj) ≅
      RHom.obj K L :=
    CochainComplex.Enriched.Over.RHom.unitAppIsoOfKInjective
      (R := A) (C := ModuleCat.{u} A) M I.obj.obj ≪≫
        RHom.mapIso eM.symm eI
  let eFM : S.obj (Fc.obj M) ≅ D.obj K :=
    (F.mapDerivedCategoryFactors.app M).symm ≪≫
      (affineEtaleModuleDerivedIso A).app (Q.obj M) ≪≫ D.mapIso eM
  let eFI : S.obj (Fc.obj I.obj.obj) ≅ D.obj L :=
    (F.mapDerivedCategoryFactors.app I.obj.obj).symm ≪≫
      (affineEtaleModuleDerivedIso A).app (Q.obj I.obj.obj) ≪≫ D.mapIso eI
  let s := RingedSite.Hom.ModuleDerived.InternalHom.liftToInjectiveModel
    (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
    (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
    (Fc.obj M) (D.obj K) eFM.hom
  let t := RingedSite.Hom.ModuleDerived.InternalHom.liftToInjectiveModel
    (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
    (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
    (Fc.obj I.obj.obj) (D.obj L) eFI.hom
  let IL := RingedSite.Hom.ModuleDerived.InternalHom.injectiveModel
    (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
    (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A))) (D.obj L)
  let H := RingedSite.Hom.ModuleDerived.InternalHom.strictInternalHom
    (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
    (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
  let p := (H.map s.op).app IL
  have hs : QuasiIso s := by
    have fac := RingedSite.Hom.ModuleDerived.InternalHom.liftToInjectiveModel_fac
      (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
      (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
      (Fc.obj M) (D.obj K) eFM.hom
    have h : IsIso (S.map s ≫
        (RingedSite.Hom.ModuleDerived.InternalHom.injectiveModelIso
          (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
          (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
          (D.obj K)).hom) := by
      rw [show S.map s ≫ _ = eFM.hom from fac]
      infer_instance
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso C s).mp
      (IsIso.of_isIso_comp_right _
        (RingedSite.Hom.ModuleDerived.InternalHom.injectiveModelIso
          (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
          (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
          (D.obj K)).hom)
  let closed : MonoidalClosed (CochainComplex C ℤ) :=
    @CochainComplex.InternalHom.monoidalClosed C
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance
      (fun _ _ _ ↦ HasColimitsOfShape.has_colimit _)
      (fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit)
      (fun _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit)
      (fun _ _ _ _ _ _ ↦ PreservesColimitsOfShape.preservesColimit)
      (fun _ ↦ PreservesColimitsOfShape.preservesColimit)
      (fun _ ↦ PreservesColimitsOfShape.preservesColimit)
  have hp : IsIso (S.map p) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso C p).mpr
    have h := @SheafOfModules.RingedSite.IHom.quasiIso_map
      _ _ _ _ _ _ _ _ closed _ _ IL IL
      inferInstance inferInstance s (𝟙 IL) hs (by infer_instance)
    dsimp only [CategoryTheory.MonoidalClosed.Source.map] at h
    erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h
  exact D.map eH.inv ≫ (affineEtaleModuleDerivedIso A).inv.app _ ≫
    F.mapDerivedCategoryFactors.hom.app _ ≫
    S.map (etaleAffineComparisonComplex M I.obj.obj) ≫
    S.map ((H.obj (op (Fc.obj M))).map t) ≫
    (@asIso _ _ _ _ (S.map p) hp).inv ≫
    (RingedSite.Hom.ModuleDerived.InternalHom.modelComparisonIso
      (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
      (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
      (D.obj K) (D.obj L)).hom

/-- Changing either derived module representative commutes with the canonical
étale evaluation comparison. -/
private theorem etaleAffineComparison_model_independent
    {A : Type u} [CommRing A] [RHom.Has (A := A)]
    {K K' L L' : DerivedCategory (ModuleCat.{u} A)}
    (f : K' ⟶ K) (g : L ⟶ L') [IsIso f] [IsIso g] :
    (affineEtaleTildeDerivedLift A).map (RHom.map f g) ≫
      etaleAffineComparison K' L' =
    etaleAffineComparison K L ≫
      RingedSite.Hom.ModuleDerived.InternalHom.map
        (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
        (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
        ((affineEtaleTildeDerivedLift A).map f)
        ((affineEtaleTildeDerivedLift A).map g) := sorry

/-- On a K-injective module model the derived comparison computes by the
localized cochain evaluation map and the actual sheaf-model transports. -/
theorem etaleAffineComparison_eq {A : Type u} [CommRing A] [RHom.Has (A := A)]
    (K L : DerivedCategory (ModuleCat.{u} A))
    (M I : CochainComplex (ModuleCat.{u} A) ℤ) [I.IsKInjective]
    (eM : DerivedCategory.Q.obj M ≅ K) (eI : DerivedCategory.Q.obj I ≅ L) :
    let D := affineEtaleTildeDerivedLift A
    let F := affineEtaleModuleFunctor A
    let Fc := F.mapHomologicalComplex (.up ℤ)
    let H := RingedSite.Hom.ModuleDerived.InternalHom.strictInternalHom
      (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
      (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
    let s := RingedSite.Hom.ModuleDerived.InternalHom.liftToInjectiveModel
      (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
      (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
      (Fc.obj M) (D.obj K)
      (F.mapDerivedCategoryFactors.inv.app M ≫
        (affineEtaleModuleDerivedIso A).hom.app (DerivedCategory.Q.obj M) ≫ D.map eM.hom)
    let t := RingedSite.Hom.ModuleDerived.InternalHom.liftToInjectiveModel
      (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
      (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
      (Fc.obj I) (D.obj L)
      (F.mapDerivedCategoryFactors.inv.app I ≫
        (affineEtaleModuleDerivedIso A).hom.app (DerivedCategory.Q.obj I) ≫ D.map eI.hom)
    D.map (RHom.unitApp M I ≫ RHom.map eM.inv eI.hom) ≫
      etaleAffineComparison K L ≫
      (RingedSite.Hom.ModuleDerived.InternalHom.modelComparisonIso
        (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
        (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
        (D.obj K) (D.obj L)).inv ≫
      DerivedCategory.Q.map
        ((H.map s.op).app
          (RingedSite.Hom.ModuleDerived.InternalHom.injectiveModel
            (J := StandardTopology.Small.topology .etale (Spec (CommRingCat.of A)))
            (O := StandardSmall.commStructureSheaf .etale (Spec (CommRingCat.of A)))
            (D.obj L))) =
    (affineEtaleModuleDerivedIso A).inv.app _ ≫
      F.mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map (etaleAffineComparisonComplex M I) ≫
      DerivedCategory.Q.map ((H.obj (op (Fc.obj M))).map t) := sorry

/-- Over a Noetherian commutative ring, the affine étale evaluation comparison
is invertible for finite cohomology in the source and finite injective dimension
in the target. -/
theorem etaleAffineComparison_isIso {A : Type u} [CommRing A] [IsNoetherianRing A]
    [RHom.Has (A := A)] (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (hL : L.HasFiniteInjectiveDimension) :
    IsIso (etaleAffineComparison K L) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.InternalHom
