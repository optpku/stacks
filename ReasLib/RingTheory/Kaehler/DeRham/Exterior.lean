/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.RingTheory.Kaehler.DeRham
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.Calculus

@[expose] public section
open CategoryTheory
universe u
namespace CrystallinePDDeRham
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The standard presentation of algebraic forms is equivalent to exterior
powers of ordinary Kähler differentials. This does not identify PD quotients. -/
noncomputable def presentation (m : ℕ) :
    KaehlerDifferential.DeRham.Form A B m ≃ₗ[B]
      exteriorPower.form B Ω[B⁄A] m :=
  LinearEquiv.ofBijective (KaehlerDifferential.DeRham.toExterior A B m).hom
    (KaehlerDifferential.DeRham.toExterior_bijective A B m)

/-- The actual algebraic de Rham differential on the exterior presentation. -/
noncomputable def algebraicFamily : DifferentialOperator.DeRham.Family A B Ω[B⁄A] :=
  fun m ↦
    { toFun := fun ω ↦ presentation A B (m + 1)
        (Submodule.Quotient.restrictScalarsEquiv A
          (KaehlerDifferential.DeRham.relations A B (m + 1))
          ((KaehlerDifferential.DeRham.rawD A B m).hom
            ((Submodule.Quotient.restrictScalarsEquiv A
              (KaehlerDifferential.DeRham.relations A B m)).symm
                ((presentation A B m).symm ω))))
      map_add' := sorry
      map_smul' := sorry }

/-- The generator formula for algebraic de Rham forms gives its differential laws. -/
theorem algebraicFamily_laws :
    DifferentialOperator.DeRham.IsDifferential (KaehlerDifferential.D A B)
      (algebraicFamily A B) := sorry

end CrystallinePDDeRham
