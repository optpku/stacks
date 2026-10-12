/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coherent.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Termwise

/-! Bounded coherent representatives selected through the actual bounded
coherent comparison and bounded homotopy localization, with their specified
localization comparison. No representation is supplied by the caller. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CoherentRepresentative

variable (X : Scheme.{u}) [IsNoetherian X]

/-- The standard derived-category model for the category of coherent sheaves. -/
instance coherentHasDerivedCategory :
    HasDerivedCategory.{u + 1} (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory :=
  HasDerivedCategory.standard _

/-- The bounded coherent comparison is an equivalence on a Noetherian scheme. -/
instance comparisonIsEquivalence :
    (DerivedCategory.Bounded.CohomologyIn.Comparison.functor
      (SheafOfModules.isCoherent X.ringCatSheaf)).IsEquivalence :=
  Scheme.coherentBoundedComparisonIsEquivalence X

/-- The chosen coherent derived model is the preimage under the named comparison. -/
def coherentModel (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    DerivedCategory.Bounded (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory :=
  (DerivedCategory.Bounded.CohomologyIn.Comparison.functor
    (SheafOfModules.isCoherent X.ringCatSheaf)).objPreimage K

/-- Bounded homotopy localization has its existing essential-surjectivity witness. -/
instance boundedLocalizationEssSurj :
    (DerivedCategory.Bounded.Qh
      (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory).EssSurj :=
  DerivedCategory.Bounded.Qh.essSurj

/-- The bounded homotopy model is selected by the bounded localization functor. -/
def homotopyModel (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    HomotopyCategory.Bounded (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory :=
  (DerivedCategory.Bounded.Qh
    (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory).objPreimage (coherentModel X K)

/-- The actual bounded termwise coherent cochain representative. -/
def complex (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    CochainComplex.BoundedTermsIn (SheafOfModules.isCoherent X.ringCatSheaf) :=
  ⟨((SheafOfModules.isCoherent X.ringCatSheaf).ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (homotopyModel X K).obj.as, sorry⟩

/-- The localization comparison is obtained from the chosen comparison
preimages and the canonical cochain/homotopy/derived factors. -/
def comparisonIso (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    DerivedCategory.Q.obj (complex X K).obj ≅
      (ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K :=
  let P := SheafOfModules.isCoherent X.ringCatSheaf
  let T := homotopyModel X K
  (P.ι.mapDerivedCategoryFactors.app T.obj.as).symm ≪≫
    P.ι.mapDerivedCategory.mapIso
      ((DerivedCategory.quotientCompQhIso P.FullSubcategory).symm.app T.obj.as) ≪≫
    P.ι.mapDerivedCategory.mapIso
      (DerivedCategory.Bounded.ι.mapIso
        ((DerivedCategory.Bounded.Qh P.FullSubcategory).objObjPreimageIso (coherentModel X K))) ≪≫
    (ambient P).mapIso
      ((DerivedCategory.Bounded.CohomologyIn.Comparison.functor P).objObjPreimageIso K)

end AlgebraicGeometry.Scheme.ModuleDerived.CoherentRepresentative
