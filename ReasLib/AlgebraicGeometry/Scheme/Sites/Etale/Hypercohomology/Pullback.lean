/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ComplexSystem
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Localization.Predicate

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable [hAdj : ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]

/-- Hypercohomology of a complex of abelian small-étale sheaves. -/
def hypercohomologyFunctor (X : Scheme.{u}) (p : ℤ)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})] :
    DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u} :=
  siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X) ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u} p

/-- The degree-`p` étale hypercohomology object of a complex. -/
def etaleHypercohomology (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ) (p : ℤ) :
    AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).obj
    ((siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X)).obj
      (DerivedCategory.Q.obj K))

/-- Hypercohomology is functorial in maps of complexes on a fixed scheme. -/
def etaleHypercohomology.map {X : Scheme.{u}}
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    {K L : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ}
    (φ : K ⟶ L) (p : ℤ) :
    etaleHypercohomology X K p ⟶ etaleHypercohomology X L p :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).map
    ((siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X)).map
      (DerivedCategory.Q.map φ))

/-- The object definition of étale hypercohomology is homology of derived sections. -/
theorem etaleHypercohomology_obj (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ℤ) (p : ℤ) :
    etaleHypercohomology X K p =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).obj
        ((siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X)).obj
          (DerivedCategory.Q.obj K)) := sorry

/-- The inverse-image functor on cochain complexes. -/
def inverseImageComplexFunctor {S T : Scheme.{u}} (f : T ⟶ S)
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
      CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) ℤ :=
  ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
    S.smallEtaleTopology T.smallEtaleTopology).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The object-level inverse image of a cochain complex. -/
abbrev inverseImageComplex {S T : Scheme.{u}} (f : T ⟶ S)
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ℤ) :
    CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) ℤ :=
  (inverseImageComplexFunctor f).obj K

/-- Exact inverse image inverts quasi-isomorphisms. -/
theorem inverseImageComplexFunctor_invertsQuasiIso {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
      (ComplexShape.up ℤ)).IsInvertedBy (inverseImageComplexFunctor f) := sorry

/-- Derived inverse image obtained from the localization universal property. -/
noncomputable def derivedInverseImage {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) :=
  Localization.lift
    (inverseImageComplexFunctor f ⋙
      (DerivedCategory.Q : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
        DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})))
    (MorphismProperty.IsInvertedBy.of_comp
      (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) (inverseImageComplexFunctor f)
      (inverseImageComplexFunctor_invertsQuasiIso f) DerivedCategory.Q)
    (DerivedCategory.Q : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}))

/-- The comparison between derived inverse image and localized cochain inverse image. -/
noncomputable def derivedInverseImageCompQIso {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}] :
    (DerivedCategory.Q : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})) ⋙
        derivedInverseImage f ≅
      inverseImageComplexFunctor f ⋙
        (DerivedCategory.Q : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})) :=
  Localization.fac
    (inverseImageComplexFunctor f ⋙
      (DerivedCategory.Q : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
        DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})))
    (MorphismProperty.IsInvertedBy.of_comp
      (HomologicalComplex.quasiIso (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
        (ComplexShape.up ℤ)) (inverseImageComplexFunctor f)
      (inverseImageComplexFunctor_invertsQuasiIso f) DerivedCategory.Q)
    (DerivedCategory.Q : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
      DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}))

/-- The underived pullback map on global étale sections. -/
def sectionsPullback {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    :
    siteAbelianSectionsFunctor S.smallEtaleTopology (globalEtale S) ⟶
      (smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
        S.smallEtaleTopology T.smallEtaleTopology ⋙
        siteAbelianSectionsFunctor T.smallEtaleTopology (globalEtale T) :=
  { app := fun F =>
      ((smallEtaleSheafAdjunction f).unit.app F).hom.app (op (globalEtale S)) ≫
        (((smallEtalePullback f).sheafPushforwardContinuousCompSheafToPresheafIso
          AddCommGrpCat.{u} S.smallEtaleTopology T.smallEtaleTopology).hom.app
          (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
            S.smallEtaleTopology T.smallEtaleTopology).obj F)).app
          (op (globalEtale S)) ≫
        (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).obj F).obj.map
            (op (globalEtalePullbackIso f).inv)
    naturality := by intro F G φ; sorry }

/-- Derived pullback on global sections. -/
noncomputable def derivedSectionsPullback {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})] :
    siteAbelianSectionsDerived S.smallEtaleTopology (globalEtale S) ⟶
      derivedInverseImage f ⋙ siteAbelianSectionsDerived T.smallEtaleTopology (globalEtale T) :=
  (siteAbelianSectionsDerived S.smallEtaleTopology (globalEtale S)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (siteAbelianSectionsFunctor S.smallEtaleTopology (globalEtale S)))
    (HomologicalComplex.quasiIso
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))
    (derivedInverseImage f ⋙ siteAbelianSectionsDerived T.smallEtaleTopology (globalEtale T))
    (by
      simpa only [inverseImageComplexFunctor, Functor.RightDerived.Cochain.toDerived,
        Functor.Derived.Cochain.toDerived, Functor.assoc] using
      (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (sectionsPullback f) (ComplexShape.up ℤ))
      (DerivedCategory.Q : CochainComplex (AddCommGrpCat.{u}) ℤ ⥤
        DerivedCategory AddCommGrpCat.{u})) ≫
      Functor.whiskerRight
        (Functor.mapHomologicalComplexCompIso
          (F := (smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
            S.smallEtaleTopology T.smallEtaleTopology)
          (G := siteAbelianSectionsFunctor T.smallEtaleTopology (globalEtale T))
          (H := (smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
            S.smallEtaleTopology T.smallEtaleTopology ⋙
            siteAbelianSectionsFunctor T.smallEtaleTopology (globalEtale T))
          (Iso.refl _) (ComplexShape.up ℤ)).inv
        (DerivedCategory.Q : CochainComplex (AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory AddCommGrpCat.{u}) ≫
      (Functor.associator
        (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℤ))
        ((siteAbelianSectionsFunctor T.smallEtaleTopology (globalEtale T)).mapHomologicalComplex
          (ComplexShape.up ℤ))
        (DerivedCategory.Q : CochainComplex (AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory AddCommGrpCat.{u})).hom ≫
      Functor.whiskerLeft
        (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℤ))
        (RightDerived.Cochain.unit
          (siteAbelianSectionsFunctor T.smallEtaleTopology (globalEtale T))) ≫
      Functor.whiskerRight (derivedInverseImageCompQIso f).inv
        (siteAbelianSectionsDerived T.smallEtaleTopology (globalEtale T)))

/-- The derived pullback satisfies its canonical right-derived factorization law. -/
theorem derivedSectionsPullback_fac {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})] :
    (RightDerived.Cochain.unit
      (siteAbelianSectionsFunctor S.smallEtaleTopology (globalEtale S))) ≫
        Functor.whiskerLeft (DerivedCategory.Q : CochainComplex
          (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}))
          (derivedSectionsPullback f) =
      Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (sectionsPullback f) (ComplexShape.up ℤ))
        (DerivedCategory.Q : CochainComplex (AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory AddCommGrpCat.{u}) ≫
      Functor.whiskerRight
        (Functor.mapHomologicalComplexCompIso
          (F := (smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
            S.smallEtaleTopology T.smallEtaleTopology)
          (G := siteAbelianSectionsFunctor T.smallEtaleTopology (globalEtale T))
          (H := (smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
            S.smallEtaleTopology T.smallEtaleTopology ⋙
            siteAbelianSectionsFunctor T.smallEtaleTopology (globalEtale T))
          (Iso.refl _) (ComplexShape.up ℤ)).inv
        (DerivedCategory.Q : CochainComplex (AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory AddCommGrpCat.{u}) ≫
      (Functor.associator
        (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℤ))
        ((siteAbelianSectionsFunctor T.smallEtaleTopology (globalEtale T)).mapHomologicalComplex
          (ComplexShape.up ℤ))
        (DerivedCategory.Q : CochainComplex (AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory AddCommGrpCat.{u})).hom ≫
      Functor.whiskerLeft
        (((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          S.smallEtaleTopology T.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℤ))
        (RightDerived.Cochain.unit
          (siteAbelianSectionsFunctor T.smallEtaleTopology (globalEtale T))) ≫
      Functor.whiskerRight (derivedInverseImageCompQIso f).inv
        (siteAbelianSectionsDerived T.smallEtaleTopology (globalEtale T)) := sorry

/-- Pullback on degree-`p` étale hypercohomology. -/
def hypercohomologyPullback {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian.{u} (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
    (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ℤ) (p : ℤ) :
    etaleHypercohomology S K p ⟶ etaleHypercohomology T (inverseImageComplex f K) p :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).map
    ((derivedSectionsPullback f).app (DerivedCategory.Q.obj K) ≫
      (siteAbelianSectionsDerived T.smallEtaleTopology (globalEtale T)).map
        ((derivedInverseImageCompQIso f).hom.app K))

end AlgebraicGeometry.Scheme.Etale

end
