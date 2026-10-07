module

public import Mathlib.Data.Countable.Defs
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Coherent.Basic

@[expose] public section

universe u

namespace IsCoherentRing

/-- Lemma 110.12.3: a countable commutative ring `R` is coherent if and only if
the countable power `ℕ → R` is a flat `R`-module. -/
@[stacks 0ALB]
theorem iff_piNat_flat {R : Type u} [CommRing R] [Countable R] :
    IsCoherentRing R ↔ Module.Flat R (ℕ → R) := sorry

end IsCoherentRing
