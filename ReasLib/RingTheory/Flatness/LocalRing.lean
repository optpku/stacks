/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Basis.LocalRing

/-!
# Flat, free, and projective modules over nilpotent local rings

The source presents a three-way equivalence.  The direct pairwise bridges are exposed alongside
the `List.TFAE` view so downstream proofs do not have to select positions from a list.
-/

@[expose] public section

universe u v

open IsLocalRing

namespace Module.Flat.LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Over a local ring with nilpotent maximal ideal, flatness is equivalent to freeness. -/
@[stacks 051G "flat-free bridge"]
theorem iff_free (h_nil : IsNilpotent (maximalIdeal R)) :
    Module.Flat R M ↔ Module.Free R M := sorry

/-- Over a local ring with nilpotent maximal ideal, flatness is equivalent to projectivity. -/
@[stacks 051G "flat-projective bridge"]
theorem iff_projective (h_nil : IsNilpotent (maximalIdeal R)) :
    Module.Flat R M ↔ Module.Projective R M := sorry

/-- Lemma 10.101.2 (Stacks `051G`): flatness, freeness, and projectivity are equivalent over a
local ring with nilpotent maximal ideal. -/
@[stacks 051G]
theorem tfae_free_projective (h_nil : IsNilpotent (maximalIdeal R)) :
    List.TFAE [Module.Flat R M, Module.Free R M, Module.Projective R M] := sorry

end Module.Flat.LocalRing
