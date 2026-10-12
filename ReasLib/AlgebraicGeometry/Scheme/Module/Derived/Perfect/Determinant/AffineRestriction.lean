/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Determinant.ScalarChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace ActualAffineRestriction

variable (X : Scheme.{u})

-- Local instance justification (defeq pin): use the ringed-space homology witness carried by the imported derived-section unit.
local instance : CategoryWithHomology X.Modules :=
  RingedSpace.ringedSpaceModules_categoryWithHomology X.toRingedSpace

-- Local instance justification (defeq pin): use the ringed-space localization model in all components of the derived-section unit.
local instance : HasDerivedCategory X.Modules :=
  RingedSpace.ringedSpaceModules_hasDerivedCategory X.toRingedSpace

def ringMap {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

abbrev evaluation (U : X.Opens) :=
  RingedSpace.moduleSectionsEvaluationFunctor X.toRingedSpace U

abbrev derived (U : X.Opens) :=
  RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U

/-- Actual restriction of sections, with its actual ring scalar map. -/
def restriction {U V : X.Opens} (h : V ≤ U) :
    evaluation X U ⟶ evaluation X V ⋙ ModuleCat.restrictScalars (ringMap X h) :=
  Functor.whiskerLeft (SheafOfModules.forget X.ringCatSheaf)
    (PresheafOfModules.restriction X.ringCatSheaf.obj (homOfLE h).op)

def complexRestriction {U V : X.Opens} (h : V ≤ U)
    (P : CochainComplex X.Modules ℤ) :
    ((evaluation X U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶
      ((ModuleCat.restrictScalars (ringMap X h)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((evaluation X V).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) where
  f n := (restriction X h).app (P.X n)
  comm' := by sorry

/-- The cochain restriction map followed by the ACTUAL derived-section unit. -/
def cochainComparison {U V : X.Opens} (h : V ≤ U) :
    RingedSpace.moduleSectionsAtOpenToDerived X.toRingedSpace U ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ DerivedCategory X.Modules) ⋙
        (derived X V ⋙ ModuleCat.derivedRestrictionOfScalars (ringMap X h)) where
  app P := DerivedCategory.Q.map (complexRestriction X h P) ≫
    (ModuleCat.derivedRestrictionComplexUnit (ringMap X h)).app
      (((evaluation X V).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
    (ModuleCat.derivedRestrictionOfScalars (ringMap X h)).map
      ((RingedSpace.moduleSectionsAtOpenDerivedUnit X.toRingedSpace V).app P)
  naturality := by sorry

/-- Derived restriction, obtained from the universal property with the
specified cochain map. No isomorphism-existence choice is used. -/
def derivedRestriction {U V : X.Opens} (h : V ≤ U) :
    derived X U ⟶ derived X V ⋙ ModuleCat.derivedRestrictionOfScalars (ringMap X h) := by
  exact @Functor.rightDerivedDesc
    (CochainComplex X.Modules ℤ) (DerivedCategory X.Modules)
    (DerivedCategory (ModuleCat Γ(X, U))) _ _ _
    (derived X U) _ DerivedCategory.Q
    (RingedSpace.moduleSectionsAtOpenDerivedUnit X.toRingedSpace U)
    (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ))
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
    (RingedSpace.moduleSectionsAtOpenDerived_isRightDerivedFunctor X.toRingedSpace U)
    (derived X V ⋙ ModuleCat.derivedRestrictionOfScalars (ringMap X h))
    (cochainComparison X h)

/-- Canonical scalar adjoint transpose of the actual derived restriction. -/
def scalarComparison {U V : X.Opens} (h : V ≤ U) (K : DerivedCategory X.Modules) :
    (ModuleCat.derivedExtensionOfScalars (ringMap X h)).obj ((derived X U).obj K) ⟶
      (derived X V).obj K :=
  (ModuleCat.derivedExtensionRestrictionHomEquiv (ringMap X h) _ _).symm
    ((derivedRestriction X h).app K)

abbrev Perfect := Scheme.PerfectDerived.TorNegOneZero X

/-- Genuine affine RΓ preserves perfect amplitude [-1,0]. -/
def affineObject (K : Perfect X) (U : X.affineOpens) : CanonicalRingDeterminant.Object Γ(X, U.1) :=
  ⟨⟨(derived X U.1).obj K.obj.obj, by sorry⟩, by sorry⟩

/-- Affine localization is flat, and perfect complexes are quasicoherent.
Invertibility is asserted for the map ALREADY constructed above. -/
instance scalarComparison_isIso (K : Perfect X) {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    IsIso (scalarComparison X h K.obj.obj) := by sorry

def affineComparison (K : Perfect X) {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    CanonicalRingDeterminant.extendedObject (ringMap X h) (affineObject X K U) ≅
      affineObject X K V :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (@asIso _ _ _ _ (scalarComparison X h K.obj.obj) (scalarComparison_isIso X K h)))

def line (K : Perfect X) (U : X.affineOpens) : ModuleCat Γ(X, U.1) :=
  ((CanonicalRingDeterminant.determinantFunctor Γ(X, U.1)).obj ⟨affineObject X K U⟩).of.obj

/-- Actual linear map after scalar extension between affine determinant lines. -/
def lineComparison (K : Perfect X) {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    (ModuleCat.extendScalars (ringMap X h)).obj (line X K U) ≅ line X K V :=
  CanonicalRingDeterminant.baseChangeIso (ringMap X h) (affineObject X K U) ≪≫
    (ObjectProperty.ι _).mapIso
      ((CanonicalRingDeterminant.determinantFunctor Γ(X, V.1)).map ⟨affineComparison X K h⟩).iso

/-- Affine determinant restriction is the ordinary scalar-adjoint transpose. -/
def lineRestriction (K : Perfect X) {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    line X K U ⟶ (ModuleCat.restrictScalars (ringMap X h)).obj (line X K V) :=
  (ModuleCat.extendRestrictScalarsAdj (ringMap X h)).homEquiv _ _ (lineComparison X K h).hom

end ActualAffineRestriction
