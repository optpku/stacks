/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite ComplexShape
noncomputable section
universe v u

namespace ActualHomDerivedExt
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable (A : C) {F : C} (I : InjectiveResolution F)

/-- The covariant additive Hom functor with the specified source object. -/
abbrev homFunctor : C ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (op A)

/-- The actual Hom complex of the degree-zero source and an injective resolution. -/
def homComplexIso :
    ((homFunctor A).mapHomologicalComplex (up ℤ)).obj I.cochainComplex ≅
      CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj A) I.cochainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (CochainComplex.HomComplex.Cochain.fromSingleEquiv
      (X := A) (K := I.cochainComplex) (zero_add i)).symm.toAddCommGrpIso)
    (fun _ _ _ ↦ sorry)

/-- The standard resolution Hom-complex comparison evaluates cocycle classes as Ext classes. -/
def classExtIso (n : ℕ) :
    AddCommGrpCat.of (CochainComplex.HomComplex.CohomologyClass
      ((CochainComplex.singleFunctor C 0).obj A) I.cochainComplex (n : ℤ)) ≅
      AddCommGrpCat.of (Ext A F n) :=
  (I.extAddEquivCohomologyClass (X := A) (n := n)).symm.toAddCommGrpIso

/-- The actual homology, cocycle-class and Ext comparisons are composed in that order. -/
def homologyExtIso (n : ℕ) :
    (((homFunctor A).mapHomologicalComplex (up ℤ)).obj I.cochainComplex).homology (n : ℤ) ≅
      AddCommGrpCat.of (Ext A F n) :=
  HomologicalComplex.homologyMapIso (homComplexIso A I) (n : ℤ) ≪≫
    (CochainComplex.HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor C 0).obj A) I.cochainComplex (n : ℤ)).toAddCommGrpIso ≪≫
    classExtIso A I n

variable [HasInjectiveResolutions C]

/-- The ordinary derived-Hom/Ext comparison uses the specified resolution computation. -/
def rightDerivedIso (n : ℕ) : ((homFunctor A).rightDerived n).obj F ≅
    AddCommGrpCat.of (Ext A F n) :=
  (InjectiveResolution.RightDerived.homologyIso I (homFunctor A) n).symm ≪≫
    homologyExtIso A I n

end ActualHomDerivedExt
