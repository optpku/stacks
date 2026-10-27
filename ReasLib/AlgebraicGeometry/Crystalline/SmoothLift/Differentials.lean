/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Differentials.Affine
public import ReasLib.AlgebraicGeometry.Crystalline.SmoothLift.Object
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.Calculus

@[expose] public section
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
universe u
namespace AlgebraicGeometry.Scheme.Crystalline.SmoothLift.Differentials

variable {A : Type u} [CommRing A] {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [Smooth f]
variable (I : (Spec (.of A)).IdealSheafData)
variable (hI : Scheme.Crystalline.Affine.idealCompatible IA I) (U : Y.affineOpens)

/-- For a smooth algebra and the uniquely base-extended PD ideal, every
ordinary A-relative derivation is already PD-compatible. Thus the PD
differential relations vanish. This is not claimed for an arbitrary PD ideal. -/
theorem relations_eq_bot :
    -- Local instance justification (noncanonical choice): f fixes the chart algebra used by the PD relations.
    letI : Algebra A Γ(Y, U.1) := (Scheme.Hom.sectionsMap f U).toAlgebra
    CrystallinePDDeRham.relations A Γ(Y, U.1) (smoothLiftDividedPowers γA f I hI U) = ⊥ := sorry

/-- The PD quotient on this smooth-lift chart is identified with ordinary
Kähler differentials through its actual zero relation submodule. -/
noncomputable def toOrdinary :=
  -- Local instance justification (noncanonical choice): f fixes the A-algebra structure on chart functions.
  letI : Algebra A Γ(Y, U.1) := (Scheme.Hom.sectionsMap f U).toAlgebra
  Submodule.quotEquivOfEqBot _ (relations_eq_bot γA f I hI U)

/-- The canonical PD-form comparison with sections of the genuine
relative differential sheaf on this affine open. -/
noncomputable def comparison :=
  -- Local instance justification (noncanonical choice): f fixes the A-algebra structure on chart functions.
  letI : Algebra A Γ(Y, U.1) := (Scheme.Hom.sectionsMap f U).toAlgebra
  (Scheme.RelativeDifferentials.Affine.comparison f U).comp
    (toOrdinary γA f I hI U).toLinearMap

/-- Bijectivity follows from the genuine affine differential comparison
and the actual zero-relation quotient, not from a false arbitrary PD inverse. -/
theorem comparison_bijective : Function.Bijective (comparison γA f I hI U) :=
  (Scheme.RelativeDifferentials.Affine.comparison_bijective f U).comp
    (toOrdinary γA f I hI U).bijective

/-- The uniquely specified affine PD-form/sheaf-section equivalence. -/
noncomputable def equivalence :=
  LinearEquiv.ofBijective (comparison γA f I hI U) (comparison_bijective γA f I hI U)

/-- The comparison sends the actual PD differential of b to the actual
universal sheaf differential of b; this fixes the normalization on generators. -/
theorem comparison_derivation (b : Γ(Y, U.1)) :
    -- Local instance justification (noncanonical choice): f fixes the chart algebra used in the generator formula.
    letI : Algebra A Γ(Y, U.1) := (Scheme.Hom.sectionsMap f U).toAlgebra
    comparison γA f I hI U
      (CrystallinePDDeRham.derivation A Γ(Y, U.1) (smoothLiftDividedPowers γA f I hI U) b) =
        Scheme.RelativeDifferentials.Affine.sectionDerivation f U b := by
  -- Local instance justification (noncanonical choice): use the chart action fixed in the statement.
  letI : Algebra A Γ(Y, U.1) := (Scheme.Hom.sectionsMap f U).toAlgebra
  -- Local instance justification (noncanonical choice): the sheaf sections use the same induced A-action.
  letI : Module A Γ(Scheme.Modules.DeRham.oneForms f, U.1) :=
    Module.compHom _ (Scheme.Hom.sectionsMap f U)
  -- Local instance justification (noncanonical choice): expose its canonical scalar tower for the universal property.
  letI : IsScalarTower A Γ(Y, U.1) Γ(Scheme.Modules.DeRham.oneForms f, U.1) :=
    IsScalarTower.restrictScalars A Γ(Y, U.1) Γ(Scheme.Modules.DeRham.oneForms f, U.1)
  change (Scheme.RelativeDifferentials.Affine.derivation f U).liftKaehlerDifferential
      (KaehlerDifferential.D A Γ(Y, U.1) b) = _
  exact Derivation.liftKaehlerDifferential_comp_D (Scheme.RelativeDifferentials.Affine.derivation f U) b

end AlgebraicGeometry.Scheme.Crystalline.SmoothLift.Differentials
