/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.DividedPowers.Basic
public import ReasLib.RingTheory.AdicCompletion.InverseSystem
public import ReasLib.RingTheory.DividedPowers.DeRham.CrystallineOmega
public import ReasLib.RingTheory.DividedPowers.Envelope.AdicCompletion
public import stacks_project.Chap60.Remark_60_6_7_Forms
public import stacks_project.Chap60.«60_17_0_2»
public import stacks_project.Chap60.«60_17_0_4»
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

/-- The completed relative divided-power differential module for the chosen
`D(n)` ring from the preceding construction. -/
noncomputable abbrev crystallineOmegaDn
    {A : Type u} [CommRing A] {D : Type v} [CommRing D]
    (f : A →+* D) (p : ℕ) [Fact (Nat.Prime p)] {J : Ideal D}
    (γbar : DividedPowers J) : Type v :=
  AdicCompletion (Ideal.span {(p : D)})
    (dividedPowerDifferential f γbar)

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

/-- The base map from `A` into the completed ring `D(n)` from the preceding construction. -/
noncomputable def crystallineDnBaseMap : A →+* crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE :=
  (algebraMap E.D (crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE)).comp
    (E.toD.comp (algebraMap A (tensorPowerCarrier A ι n)))

/-- The induced divided-power ideal `J̄(n)` on `D(n)`. -/
noncomputable abbrev crystallineDnIdeal :
    Ideal (crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE) :=
  Ideal.map (algebraMap E.D (crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE)) E.D.ideal

variable (γbar : DividedPowers
  (crystallineDnIdeal p I γ π hπ n hIC hpnil J hJ hIJ E hE))

/- 60.17.0.5 (1): The completed relative divided-power differential module on
`D(n)` is canonically isomorphic to the inverse limit of actual quotient-ring
differential modules, indexed by the canonical stable cofinal tail. -/
@[stacks 07L0] #check (crystallineOmegaD_actualLimitIso
    (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE) γbar p
    (nilpotencyClass (p : C))
    (DividedPowerEnvelope.primePowLeCompletionIdeal γ
      (algebraMap A (tensorPowerCarrier A ι n)) hIJ E
      (tensorPowerAlgHom π n).toRingHom hJ p hpnil) :
    ModuleCat.of (crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE)
        (crystallineOmegaDn
          (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE) p γbar) ≅
      limit (CrystallineOmega.actualSystem
        (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE) γbar p
        (nilpotencyClass (p : C))
        (DividedPowerEnvelope.primePowLeCompletionIdeal γ
          (algebraMap A (tensorPowerCarrier A ι n)) hIJ E
          (tensorPowerAlgHom π n).toRingHom hJ p hpnil)))

/- 60.17.0.5 (2): The completed relative divided-power differential module on
`D(n)` is canonically isomorphic to the inverse limit of its positive
`p`-power quotient system.
-/
@[stacks 07L0] #check (crystallineOmegaD_limitIso
    (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE) γbar p :
    ModuleCat.of (crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE)
        (crystallineOmegaDn
          (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE) p γbar) ≅
      limit (AdicCompletion.positiveQuotientSystem
        (Ideal.span {(p : crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE)})
        (dividedPowerDifferential
          (crystallineDnBaseMap p I γ π hπ n hIC hpnil J hJ hIJ E hE) γbar)))

end CrystallineDnSetup
