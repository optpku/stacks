/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.«60_17_0_5»
import ReasLib.RingTheory.DividedPowers.DeRham.CrystallineOmega
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

section CrystallineDnSetup

variable {A : Type u} [CommRing A]
variable (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π) (n : ℕ)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (J : Ideal (tensorPowerCarrier A ι n))
variable (hJ : J = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
variable (hIJ : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ J)
variable (E : DividedPowerEnvelope I γ
  (algebraMap A (tensorPowerCarrier A ι n)) J hIJ)
variable (hE : DividedPowerEnvelope.IsUniversal γ
  (algebraMap A (tensorPowerCarrier A ι n)) hIJ E)
variable (γbar : DividedPowers
  (crystallineDnIdeal p I γ π hπ n hIC hpnil J hJ hIJ E hE))

/- 60.17.0.6: The compatible stage derivations induce the completed divided-power
derivation `d : D(n) → Ω_{D(n)}`, represented as a bundled derivation over `A`. -/
@[stacks 07L1] #check (crystallineOmegaD_derivation
    (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE) γbar p :
    -- Local instance justification (instance diamond): f.toAlgebra pins Algebra A D(n) to the source base map, avoiding a competing algebra instance.
    letI : Algebra A (crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE) :=
      (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE).toAlgebra
    Derivation A (crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE)
      (crystallineOmegaDn
        (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE) p γbar))

/- Elementwise formula for the completed divided-power derivation on `D(n)`. -/
#check (crystallineOmegaD_derivation_apply
    (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE) γbar p :
    ∀ b : crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE,
    -- Local instance justification (instance diamond): f.toAlgebra pins Algebra A D(n) to the source base map, avoiding a competing algebra instance.
    letI : Algebra A (crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE) :=
      (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE).toAlgebra
    crystallineOmegaD_derivation
        (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE) γbar p b =
      AdicCompletion.of
        (Ideal.span {(p : crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE)})
        (dividedPowerDifferential
          (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE) γbar)
        (dividedPowerDifferentialDerivation
          (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE) γbar b))

end CrystallineDnSetup
