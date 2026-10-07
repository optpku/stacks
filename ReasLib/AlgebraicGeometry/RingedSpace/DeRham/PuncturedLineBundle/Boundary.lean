module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.Exact
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.LogarithmicNormalization
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.FirstChern
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

@[expose] public section

open CategoryTheory ComplexShape
open AlgebraicGeometry Scheme.DeRham Scheme.DeRham.DerivedPushforward

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle

-- Local instance justification (defeq pin): localization and the connecting morphism use the canonical module-sheaf derived category of DerivedPushforward.derivedComplex.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules)
variable [Scheme.Modules.Invertible ℒ]
variable (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
variable [Scheme.IsRelativeSpectrumOver P] (D : WeightZeroDeRham f ℒ P)

/-- The residue short complex shifted by one, whose quotient identifies with ordinary forms. -/
noncomputable def shiftedSequence :=
  (sequence f ℒ P D).map (shiftFunctor _ (1 : ℤ))

/-- Shifting the short exact residue sequence preserves short exactness. -/
theorem shiftedSequence_shortExact (hD : (sequence f ℒ P D).ShortExact) :
    (shiftedSequence f ℒ P D).ShortExact := sorry

/-- The connecting map of the shifted residue sequence, transported to a degree-two
endomorphism of the localized ordinary de Rham complex. -/
noncomputable def boundary (hD : (sequence f ℒ P D).ShortExact) :
    ShiftedHom (derivedComplex f) (derivedComplex f) (2 : ℤ) :=
  let K := ordinaryComplex f
  let e : derivedComplex f ≅ DerivedCategory.Q.obj K :=
    (DerivedCategory.quotientCompQhIso (Modules f.toLRSHom.toShHom)).app K
  e.hom ≫ DerivedCategory.Q.map (shiftNegShift K (1 : ℤ)).inv ≫
    DerivedCategory.triangleOfSESδ (shiftedSequence_shortExact f ℒ P D hD) ≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K)⟦(1 : ℤ)⟧' ≫
        e.inv⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫
          (shiftFunctorAdd' _ (1 : ℤ) (1 : ℤ) (2 : ℤ) rfl).inv.app (derivedComplex f)

/-- The boundary is the explicit localization-and-shift transport of the shifted connecting map. -/
theorem boundary_def (hD : (sequence f ℒ P D).ShortExact) :
    boundary f ℒ P D hD =
      let K := ordinaryComplex f
      let e : derivedComplex f ≅ DerivedCategory.Q.obj K :=
        (DerivedCategory.quotientCompQhIso (Modules f.toLRSHom.toShHom)).app K
      e.hom ≫ DerivedCategory.Q.map (shiftNegShift K (1 : ℤ)).inv ≫
        DerivedCategory.triangleOfSESδ (shiftedSequence_shortExact f ℒ P D hD) ≫
          ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K)⟦(1 : ℤ)⟧' ≫
            e.inv⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧' ≫
              (shiftFunctorAdd' _ (1 : ℤ) (1 : ℤ) (2 : ℤ) rfl).inv.app
                (derivedComplex f) := sorry

/-- For the geometric logarithmic normalization, the shifted residue boundary is the
canonical action of the independently constructed relative de Rham first Chern class. -/
theorem boundary_eq_classAction (hD : IsGeometric f ℒ P D) :
    boundary f ℒ P D (puncturedLineBundleSequence_shortExact f ℒ P D) =
      CanonicalAction.map f 2 (Scheme.DeRham.firstChernClass f ℒ) := sorry

end AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle
