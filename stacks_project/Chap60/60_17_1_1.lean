/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.IdealPower.AdicCompletion
public import stacks_project.Chap60.«60_17_0_4»
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CommRingCat.IdealPower
open Opposite

universe u

variable {A : Type u} [CommRing A]
    (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I)
    {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    (hπ : Function.Surjective π) (n : ℕ)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
    (hpnil : IsNilpotent (p : C))
    (J : Ideal (tensorPowerCarrier A ι n))
    (hJ : J = RingHom.ker (tensorPowerAlgHom π n).toRingHom)
    (hIJ : Ideal.map (algebraMap A (tensorPowerCarrier A ι n)) I ≤ J)
    (E : DividedPowerEnvelope I γ
      (algebraMap A (tensorPowerCarrier A ι n)) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (tensorPowerCarrier A ι n)) hIJ E)

/- 60.17.1.1: `crystallineDn` is the inverse limit of the positive `p`-power quotient rings
of its divided-power envelope. -/
@[stacks 07L3]
#check
  (CategoryTheory.CommRingCat.IdealPower.Positive.adicCompletionLimitIso
    (Ideal.span {(p : E.D)}) :
      CommRingCat.of (crystallineDn p I γ π hπ n hIC hpnil J hJ hIJ E hE) ≅
        limit (CategoryTheory.CommRingCat.IdealPower.Positive.system
          (Ideal.span {(p : E.D)})))
