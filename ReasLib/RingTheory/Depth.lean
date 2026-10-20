/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Depth of Modules

@stack 00LI

The depth of a module `M` with respect to an ideal `I` is the supremum of the lengths
of `M`-regular sequences contained in `I`. When the module equals `IM`, the depth is `∞`.

In the local case, the depth of `M` is the depth with respect to the maximal ideal.

## Main definitions

* `Ideal.regularSequenceLengths` — the set of lengths of regular sequences in an ideal.
* `Ideal.depth` — depth of a module with respect to an ideal.
* `moduleDepth` — depth of a module over a local ring (with respect to the maximal ideal).
-/

universe u v

open RingTheory.Sequence
open scoped ENat

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The set of lengths of `M`-regular sequences whose terms all lie in the ideal `I`. -/
def regularSequenceLengths (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    Set ℕ∞ :=
  {d | ∃ rs : List R, IsRegular M rs ∧ Ideal.ofList rs ≤ I ∧ d = rs.length}

/-- The `I`-depth of `M` is `∞` when `IM = M`, and otherwise it
is the supremum of the lengths of `M`-regular sequences contained in `I`. -/
@[stacks 00LI]
noncomputable def depth (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : ℕ∞ :=
  if I • (⊤ : Submodule R M) = ⊤ then ⊤
  else sSup (regularSequenceLengths I M)

/-- If `IM = M`, then the `I`-depth of `M` is infinite. -/
@[simp]
theorem depth_eq_top_of_smul_top (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M]
    (hIM : I • (⊤ : Submodule R M) = ⊤) : depth I M = ⊤ := sorry

/-- If `IM ≠ M`, then the `I`-depth is the supremum of regular sequence lengths. -/
theorem depth_eq_sSup_lengths_of_smul_top_ne_top (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) :
    depth I M = sSup (regularSequenceLengths I M) := sorry

end Ideal

section

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- In a local ring, the depth of `M` is the depth with respect to the maximal ideal. -/
@[stacks 00LI "local module depth"]
noncomputable abbrev moduleDepth (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : ℕ∞ :=
  Ideal.depth (maximalIdeal R) M

/-- A subsingleton module over a local ring has infinite depth. -/
@[stacks 00LI "depth of a subsingleton module"]
theorem moduleDepth_eq_top_of_subsingleton
    {M : Type v} [AddCommGroup M] [Module R M] [Subsingleton M] :
    moduleDepth R M = ⊤ := sorry

end
