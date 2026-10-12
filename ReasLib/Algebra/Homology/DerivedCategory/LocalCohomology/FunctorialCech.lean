/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.OrderedCech
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.RingTheory.Ideal.FiniteGeneration.Family

@[expose] public section

noncomputable section

open CategoryTheory
open ComplexShape

universe u v

namespace CategoryTheory.DerivedCategory.LocalCohomology

/-- A coherent choice of augmented complexes for finitely generated ideals, with transitions,
derived base change, and comparison with every ordered finite localization Čech complex. -/
structure FunctorialCechComplex where
  /-- The cochain complex attached to a finitely generated ideal. -/
  obj : {A : Type v} → [CommRing A] → (I : {I : Ideal A // I.FG}) →
    CochainComplex (ModuleCat A) ℤ
  /-- The augmentation to the regular module concentrated in degree zero. -/
  augmentation : {A : Type v} → [CommRing A] → (I : {I : Ideal A // I.FG}) →
    obj I ⟶ (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A)
  /-- The transition map into restriction of scalars along a ring homomorphism. -/
  transition : {A B : Type v} → [CommRing A] → [CommRing B] →
    (f : A →+* B) → (I : {I : Ideal A // I.FG}) →
    (J : {J : Ideal B // J.FG}) → I.1.map f = J.1 →
      ((obj I : CochainComplex (ModuleCat A) ℤ) ⟶
        ((ModuleCat.restrictScalars f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (obj J))
  /-- Transition maps commute with the augmentations. -/
  transition_augmentation : ∀ {A B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
    (hIJ : I.1.map f = J.1),
      transition f I J hIJ ≫
          ((ModuleCat.restrictScalars f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (augmentation J) =
        augmentation I ≫
          (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).map
            (ModuleCat.semilinearMapAddEquiv f (ModuleCat.of A A)
              (ModuleCat.of B B) f.toSemilinearMap) ≫
          (Functor.mapCochainComplexSingleFunctor
            (ModuleCat.restrictScalars f) (0 : ℤ)).inv.app (ModuleCat.of B B)
  /-- Transition maps compose through the canonical comparison of restriction functors. -/
  transition_comp : ∀ {A B C : Type v} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (I : {I : Ideal A // I.FG})
    (J : {J : Ideal B // J.FG}) (K : {K : Ideal C // K.FG})
    (hIJ : I.1.map f = J.1) (hJK : J.1.map g = K.1)
    (hIK : I.1.map (g.comp f) = K.1),
      transition f I J hIJ ≫
          ((ModuleCat.restrictScalars f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (transition g J K hJK) ≫
          (Functor.mapHomologicalComplexCompIso
            (ModuleCat.restrictScalarsComp f g).symm
            (ComplexShape.up ℤ)).hom.app (obj K) =
        transition (g.comp f) I K hIK
  /-- The adjoint transition becomes an isomorphism in the derived category. -/
  derivedBaseChange : ∀ {A B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
    (hIJ : I.1.map f = J.1),
      IsIso
        ((ModuleCat.derivedExtensionComplexCounit f).app (obj I) ≫
          (DerivedCategory.Q : CochainComplex (ModuleCat B) ℤ ⥤
            DerivedCategory (ModuleCat B)).map
            (((Adjunction.mapHomologicalComplexAdjunction
              (ModuleCat.extendRestrictScalarsAdj f) (ComplexShape.up ℤ)).homEquiv
                (obj I) (obj J)).symm (transition f I J hIJ)))
  /-- The comparison with the ordered localization Čech complex of a generating family. -/
  cechComparison : {A : Type v} → [CommRing A] → (I : {I : Ideal A // I.FG}) →
    (G : I.1.FiniteGeneratingFamily) →
      OrderedCech.source G.generator ≅
        (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤
          DerivedCategory (ModuleCat A)).obj (obj I)
  /-- The Čech comparison commutes with the augmentation projections. -/
  cechComparison_augmentation : ∀ {A : Type v} [CommRing A]
    (I : {I : Ideal A // I.FG}) (G : I.1.FiniteGeneratingFamily),
      (cechComparison I G).hom ≫
          (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤
            DerivedCategory (ModuleCat A)).map (augmentation I) =
        OrderedCech.derivedProjection G.generator

/-- Construct a coherent Čech-complex choice from its concrete data and compatibility laws. -/
def FunctorialCechComplex.of
    (object : {A : Type u} → [CommRing A] → (I : {I : Ideal A // I.FG}) →
      CochainComplex (ModuleCat A) ℤ)
    (augment : {A : Type u} → [CommRing A] → (I : {I : Ideal A // I.FG}) →
      object I ⟶ (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A A))
    (map : {A B : Type u} → [CommRing A] → [CommRing B] →
      (f : A →+* B) → (I : {I : Ideal A // I.FG}) →
      (J : {J : Ideal B // J.FG}) → I.1.map f = J.1 →
        (object I ⟶ ((ModuleCat.restrictScalars f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (object J)))
    (map_augment : ∀ {A B : Type u} [CommRing A] [CommRing B]
      (f : A →+* B) (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
      (hIJ : I.1.map f = J.1),
        map f I J hIJ ≫
            ((ModuleCat.restrictScalars f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (augment J) =
          augment I ≫
            (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).map
              (ModuleCat.semilinearMapAddEquiv f (ModuleCat.of A A)
                (ModuleCat.of B B) f.toSemilinearMap) ≫
            (Functor.mapCochainComplexSingleFunctor
              (ModuleCat.restrictScalars f) (0 : ℤ)).inv.app (ModuleCat.of B B))
    (map_comp : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C) (I : {I : Ideal A // I.FG})
      (J : {J : Ideal B // J.FG}) (K : {K : Ideal C // K.FG})
      (hIJ : I.1.map f = J.1) (hJK : J.1.map g = K.1)
      (hIK : I.1.map (g.comp f) = K.1),
        map f I J hIJ ≫
            ((ModuleCat.restrictScalars f).mapHomologicalComplex
              (ComplexShape.up ℤ)).map (map g J K hJK) ≫
            (Functor.mapHomologicalComplexCompIso
              (ModuleCat.restrictScalarsComp f g).symm
              (ComplexShape.up ℤ)).hom.app (object K) =
          map (g.comp f) I K hIK)
    (map_isIso : ∀ {A B : Type u} [CommRing A] [CommRing B]
      (f : A →+* B) (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
      (hIJ : I.1.map f = J.1),
        IsIso
          ((ModuleCat.derivedExtensionComplexCounit f).app (object I) ≫
            (DerivedCategory.Q : CochainComplex (ModuleCat B) ℤ ⥤
              DerivedCategory (ModuleCat B)).map
              (((Adjunction.mapHomologicalComplexAdjunction
                (ModuleCat.extendRestrictScalarsAdj f) (ComplexShape.up ℤ)).homEquiv
                  (object I) (object J)).symm (map f I J hIJ))))
    (cechMap : {A : Type u} → [CommRing A] → (I : {I : Ideal A // I.FG}) →
      (G : I.1.FiniteGeneratingFamily) →
        OrderedCech.source G.generator ≅
          (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤
            DerivedCategory (ModuleCat A)).obj (object I))
    (cechMap_augment : ∀ {A : Type u} [CommRing A]
      (I : {I : Ideal A // I.FG}) (G : I.1.FiniteGeneratingFamily),
        (cechMap I G).hom ≫
            (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤
              DerivedCategory (ModuleCat A)).map (augment I) =
          OrderedCech.derivedProjection G.generator) :
    FunctorialCechComplex.{u} where
  obj := object
  augmentation := augment
  transition := map
  transition_augmentation := map_augment
  transition_comp := map_comp
  derivedBaseChange := map_isIso
  cechComparison := cechMap
  cechComparison_augmentation := cechMap_augment

/-- The derived base-change morphism attached to a transition of a coherent Čech choice. -/
noncomputable def FunctorialCechComplex.baseChange
    (F : FunctorialCechComplex.{u}) {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
    (hIJ : I.1.map f = J.1) :
    (ModuleCat.derivedExtensionOfScalars f).obj
      ((DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤
        DerivedCategory (ModuleCat A)).obj (F.obj I)) ⟶
      (DerivedCategory.Q : CochainComplex (ModuleCat B) ℤ ⥤
        DerivedCategory (ModuleCat B)).obj (F.obj J) :=
  (ModuleCat.derivedExtensionComplexCounit f).app (F.obj I) ≫
    (DerivedCategory.Q : CochainComplex (ModuleCat B) ℤ ⥤
      DerivedCategory (ModuleCat B)).map
      (((Adjunction.mapHomologicalComplexAdjunction
        (ModuleCat.extendRestrictScalarsAdj f) (ComplexShape.up ℤ)).homEquiv
          (F.obj I) (F.obj J)).symm (F.transition f I J hIJ))

/-- The transition law consists of augmentation compatibility and invertibility after derived
base change. -/
theorem FunctorialCechComplex.transition_spec
    (F : FunctorialCechComplex.{u}) {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
    (hIJ : I.1.map f = J.1) :
    (F.transition f I J hIJ ≫
        ((ModuleCat.restrictScalars f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (F.augmentation J) =
      F.augmentation I ≫
        (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).map
          (ModuleCat.semilinearMapAddEquiv f (ModuleCat.of A A)
            (ModuleCat.of B B) f.toSemilinearMap) ≫
        (Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars f) (0 : ℤ)).inv.app (ModuleCat.of B B)) ∧
      IsIso (F.baseChange f I J hIJ) := sorry

/-- In a fixed universe, coherent augmented Čech complexes exist for all finitely generated ideals. -/
theorem existsFunctorialCechComplex : Nonempty (FunctorialCechComplex.{u}) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
