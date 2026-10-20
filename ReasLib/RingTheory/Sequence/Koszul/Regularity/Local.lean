/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Sequence.QuasiRegular.MaximalIdeal
public import ReasLib.RingTheory.Sequence.QuasiRegular.Regularity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Koszul regularity over Noetherian local rings

For a finite family in the maximal ideal, the regular, Koszul-regular, `H₁`-regular, and
quasi-regular conditions agree on a nonzero finite module.

@stack 09CC
-/

@[expose] public section

noncomputable section

universe u

namespace RingTheory.Sequence.Regularity

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Lemma 15.30.7 (1): on a nonzero finite module over a Noetherian local ring, the four standard
regularity conditions agree for a finite family in the maximal ideal. -/
@[stacks 09CC "Lemma 15.30.7 (1)"]
theorem local_tfae {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] {r : ℕ} (f : Fin r → R)
    (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal R) :
    List.TFAE
      [IsRegular M (List.ofFn f), IsKoszulRegularOn M f, IsH1RegularOn M f,
        IsQuasiRegular M (List.ofFn f)] := sorry

/-- Lemma 15.30.7 (2): for the regular module, regularity, Koszul-regularity, `H₁`-regularity,
and quasi-regularity agree for a finite family in the maximal ideal. -/
@[stacks 09CC "Lemma 15.30.7 (2)"]
theorem localSequence_tfae {r : ℕ} (f : Fin r → R)
    (hf : ∀ i, f i ∈ IsLocalRing.maximalIdeal R) :
    List.TFAE
      [IsRegular R (List.ofFn f), IsKoszulRegularSequence f, IsH1RegularSequence f,
        IsQuasiRegularSequence (List.ofFn f)] := sorry

end RingTheory.Sequence.Regularity
