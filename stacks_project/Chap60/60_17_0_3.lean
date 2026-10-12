/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.«60_17_0_2»
public import ReasLib.RingTheory.DividedPowers.DeRham.CrystallineOmega
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

/- The source equation `d : D ⟶ Ω_D` is represented by the bundled relative
   derivation obtained from the preceding divided-power derivation and the
   canonical map into the adic completion. -/

/- 60.17.0.3: The compatible stage derivations induce the completed divided-power
derivation d : D → Ω_D, represented as a bundled derivation over A. -/
@[stacks 07JA] #check (crystallineOmegaD_derivation :
  ∀ {A : Type u} [CommRing A] {D : Type v} [CommRing D]
    (f : A →+* D) {J : Ideal D} (γbar : DividedPowers J)
    (p : ℕ) [Fact (Nat.Prime p)],
    -- Local instance justification (instance diamond): f.toAlgebra selects the scalar action of the explicit ring map in the relative Derivation type.
    letI : Algebra A D := f.toAlgebra
    Derivation A D (crystallineOmegaD f γbar p))

/- Elementwise formula for the completed divided-power derivation. -/
#check (crystallineOmegaD_derivation_apply :
  ∀ {A : Type u} [CommRing A] {D : Type v} [CommRing D]
    (f : A →+* D) {J : Ideal D} (γbar : DividedPowers J)
    (p : ℕ) [Fact (Nat.Prime p)] (b : D),
    -- Local instance justification (instance diamond): f.toAlgebra fixes the explicit ring-map-selected scalar action in the derivation and its elementwise formula.
    letI : Algebra A D := f.toAlgebra
    crystallineOmegaD_derivation f γbar p b =
      AdicCompletion.of (Ideal.span {(p : D)})
        (KaehlerDifferential.DeRham.dividedPowerDifferential f γbar)
        (KaehlerDifferential.DeRham.dividedPowerDifferentialDerivation f γbar b))
