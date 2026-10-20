/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.RingTheory.Completion.LocalRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Detecting non-pth-powers by derivations

An element of a characteristic-`p` domain that is not a `p`th power in the fraction field is
detected by an absolute derivation when the domain is of finite type over a Noetherian complete
local ring.

@stack 07PH
-/

@[expose] public section

universe u v

namespace Derivation

/-- Lemma 15.48.5 (Stacks `07PH`): let `B` be a characteristic-`p` domain of finite type over
some Noetherian complete local ring. If `f : B` is not a `p`th power in `FractionRing B`, then
an absolute derivation of `B` has nonzero value at `f`. -/
@[stacks 07PH]
theorem exists_apply_ne_zero_of_not_exists_pthRoot
    {B : Type u} [CommRing B] [IsDomain B]
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (hB :
      ∃ (R : Type v) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : IsCompleteLocalRing R)
        (_ : Algebra R B), Algebra.FiniteType R B)
    (f : B)
    (hf : ¬ ∃ g : FractionRing B, g ^ p = algebraMap B (FractionRing B) f) :
    ∃ D : Derivation ℤ B B, D f ≠ 0 := sorry

end Derivation
