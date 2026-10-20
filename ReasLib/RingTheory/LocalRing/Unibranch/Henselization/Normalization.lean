/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.LocalRing.Unibranch
public import ReasLib.RingTheory.LocalRing.Unibranch.Henselization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Normalization after Henselization

For a local ring `A` and a Henselization `Ah`, this leaf records the maximal- and minimal-prime
geometry of `Unibranch.normalization A ⊗[A] Ah`.

@stack 0C24
-/

@[expose] public section

open Ideal
open scoped TensorProduct

universe u v

noncomputable section

namespace Unibranch.Henselization

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/-- The base change of the normalization of `A_red` to a Henselization of `A`. -/
@[stacks 0C24 "normalization base change"]
abbrev normalizationBaseChange := Unibranch.normalization A ⊗[A] Ah

/-- The canonical ring map from the normalization into its Henselization base change. -/
@[stacks 0C24 "left normalization map"]
abbrev normalizationMap :
    Unibranch.normalization A →+* normalizationBaseChange (A := A) (Ah := Ah) :=
  Algebra.TensorProduct.includeLeftRingHom

/-- The canonical ring map from the Henselization into the normalization base change. -/
@[stacks 0C24 "right Henselization map"]
abbrev henselizationMap : Ah →+* normalizationBaseChange (A := A) (Ah := Ah) :=
  (Algebra.TensorProduct.includeRight :
    Ah →ₐ[A] normalizationBaseChange (A := A) (Ah := Ah)).toRingHom

/-- Lemma 15.107.2 (1), Stacks `0C24`: contraction along `normalizationMap` is a bijection on
maximal ideals. -/
@[stacks 0C24 "(1), maximal ideals"]
theorem maximalIdeals_bijOn (hfinite : (minimalPrimes A).Finite) :
    Set.BijOn (Ideal.comap (normalizationMap (A := A) (Ah := Ah)))
      {m : Ideal (normalizationBaseChange (A := A) (Ah := Ah)) | m.IsMaximal}
      {m : Ideal (Unibranch.normalization A) | m.IsMaximal} := sorry

/-- Lemma 15.107.2 (2), Stacks `0C24`: contraction along `henselizationMap` is a bijection on
minimal primes. -/
@[stacks 0C24 "(2), minimal primes"]
theorem minimalPrimes_bijOn (hfinite : (minimalPrimes A).Finite) :
    Set.BijOn (Ideal.comap (henselizationMap (A := A) (Ah := Ah)))
      (minimalPrimes (normalizationBaseChange (A := A) (Ah := Ah)))
      (minimalPrimes Ah) := sorry

/-- Lemma 15.107.2 (3), Stacks `0C24`: every minimal prime of the normalization base change lies
in a unique maximal ideal. -/
@[stacks 0C24 "(3), unique maximal ideal above a minimal prime"]
theorem minimalPrime_existsUnique_maximalIdeal
    (hfinite : (minimalPrimes A).Finite)
    {p : Ideal (normalizationBaseChange (A := A) (Ah := Ah))}
    (hp : p ∈ minimalPrimes (normalizationBaseChange (A := A) (Ah := Ah))) :
    ∃! m : Ideal (normalizationBaseChange (A := A) (Ah := Ah)), m.IsMaximal ∧ p ≤ m := sorry

/-- Lemma 15.107.2 (4), Stacks `0C24`: every maximal ideal of the normalization base change
contains a unique minimal prime. -/
@[stacks 0C24 "(4), unique minimal prime below a maximal ideal"]
theorem maximalIdeal_existsUnique_minimalPrime
    (hfinite : (minimalPrimes A).Finite)
    {m : Ideal (normalizationBaseChange (A := A) (Ah := Ah))} (hm : m.IsMaximal) :
    ∃! p : Ideal (normalizationBaseChange (A := A) (Ah := Ah)),
      p ∈ minimalPrimes (normalizationBaseChange (A := A) (Ah := Ah)) ∧ p ≤ m := sorry

end Unibranch.Henselization
