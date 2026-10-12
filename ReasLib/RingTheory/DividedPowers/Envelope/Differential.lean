/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Universal
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

open scoped TensorProduct

universe u

namespace DividedPowerEnvelope

/-- The canonical `E.D`-linear comparison from base-changed Kähler differentials
to the divided-power differential module of an explicit envelope. -/
noncomputable def differentialComparison
    {A B : Type u} [CommRing A] [CommRing B]
    {I : Ideal A} {γ : DividedPowers I} {f : A →+* B}
    {J : Ideal B} {hIJ : Ideal.map f I ≤ J}
    (E : DividedPowerEnvelope I γ f J hIJ) :
    -- Local instance justification (noncanonical choice): the explicit ring map f selects the A-algebra structure on B required by KaehlerDifferential A B; competing ring maps need not give the same structure.
    letI : Algebra A B := f.toAlgebra
    -- Local instance justification (noncanonical choice): use the explicit map `E.toD` to define the `B`-algebra structure on `E.D`.
    letI : Algebra B E.D := E.toD.toAlgebra
    -- Local instance justification (noncanonical choice): use the composite explicit map `E.toD.comp f` to define the `A`-algebra structure on `E.D`.
    letI : Algebra A E.D := (E.toD.comp f).toAlgebra
    -- Local instance justification (defeq pin): identify the composite scalar action through `B` with the pinned `A`-algebra structure on `E.D`.
    letI : IsScalarTower A B E.D := IsScalarTower.of_algebraMap_eq' rfl
    E.D ⊗[B] KaehlerDifferential A B →ₗ[E.D]
      KaehlerDifferential.DeRham.dividedPowerDifferential
        (E.toD.comp f) E.D.dividedPowers :=
  -- Local instance justification (noncanonical choice): the explicit ring map f selects the A-algebra structure on B required by KaehlerDifferential A B; competing ring maps need not give the same structure.
  letI : Algebra A B := f.toAlgebra
  -- Local instance justification (noncanonical choice): use the explicit map `E.toD` to define the `B`-algebra structure on `E.D`.
  letI : Algebra B E.D := E.toD.toAlgebra
  -- Local instance justification (noncanonical choice): use the composite explicit map `E.toD.comp f` to define the `A`-algebra structure on `E.D`.
  letI : Algebra A E.D := (E.toD.comp f).toAlgebra
  -- Local instance justification (defeq pin): identify the composite scalar action through `B` with the pinned `A`-algebra structure on `E.D`.
  letI : IsScalarTower A B E.D := IsScalarTower.of_algebraMap_eq' rfl
  (KaehlerDifferential.DeRham.dividedPowerRelations
      (E.toD.comp f) E.D.dividedPowers).mkQ.comp
    (KaehlerDifferential.mapBaseChange A B E.D)

/-- On differential generators, the canonical comparison sends `d ⊗ₜ d b` to
`d • d(E.toD b)`. -/
theorem differentialComparison_tmul
    {A B : Type u} [CommRing A] [CommRing B]
    {I : Ideal A} {γ : DividedPowers I} {f : A →+* B}
    {J : Ideal B} {hIJ : Ideal.map f I ≤ J}
    (E : DividedPowerEnvelope I γ f J hIJ) (d : E.D) (b : B) :
    -- Local instance justification (noncanonical choice): the explicit ring map f selects the A-algebra structure on B required by KaehlerDifferential A B; competing ring maps need not give the same structure.
    letI : Algebra A B := f.toAlgebra
    -- Local instance justification (noncanonical choice): use the explicit map `E.toD` to define the `B`-algebra structure on `E.D`.
    letI : Algebra B E.D := E.toD.toAlgebra
    -- Local instance justification (noncanonical choice): use the composite explicit map `E.toD.comp f` to define the `A`-algebra structure on `E.D`.
    letI : Algebra A E.D := (E.toD.comp f).toAlgebra
    -- Local instance justification (defeq pin): identify the composite scalar action through `B` with the pinned `A`-algebra structure on `E.D`.
    letI : IsScalarTower A B E.D := IsScalarTower.of_algebraMap_eq' rfl
    differentialComparison E (d ⊗ₜ[B] KaehlerDifferential.D A B b) =
      d • KaehlerDifferential.DeRham.dividedPowerDifferentialDerivation
        (E.toD.comp f) E.D.dividedPowers (E.toD b) := sorry

/-- For a universal divided-power envelope, the canonical differential comparison
is bijective, giving the differential-module identification. -/
theorem differentialComparison_bijective
    {A B : Type u} [CommRing A] [CommRing B]
    {I : Ideal A} (γ : DividedPowers I) (f : A →+* B)
    {J : Ideal B} (hIJ : Ideal.map f I ≤ J)
    (E : DividedPowerEnvelope I γ f J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ f hIJ E) :
    -- Local instance justification (noncanonical choice): the explicit ring map f selects the A-algebra structure on B required by KaehlerDifferential A B; competing ring maps need not give the same structure.
    letI : Algebra A B := f.toAlgebra
    -- Local instance justification (noncanonical choice): use the explicit map `E.toD` to define the `B`-algebra structure on `E.D`.
    letI : Algebra B E.D := E.toD.toAlgebra
    -- Local instance justification (noncanonical choice): use the composite explicit map `E.toD.comp f` to define the `A`-algebra structure on `E.D`.
    letI : Algebra A E.D := (E.toD.comp f).toAlgebra
    -- Local instance justification (defeq pin): identify the composite scalar action through `B` with the pinned `A`-algebra structure on `E.D`.
    letI : IsScalarTower A B E.D := IsScalarTower.of_algebraMap_eq' rfl
    Function.Bijective (differentialComparison E) := sorry

end DividedPowerEnvelope
