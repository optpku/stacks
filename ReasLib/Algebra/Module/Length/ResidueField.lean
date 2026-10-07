module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Length of modules supported at one maximal ideal

This leaf owns the residue-field description of a module annihilated by a maximal ideal.
`Module.IsTorsionBySet` is the canonical input: it records the scalar action directly and supplies
the quotient-ring module structure without making that derived instance part of every theorem.

@stack 00IY
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {m : Ideal R}

/-- An ideal annihilates the whole module exactly when the module is torsion by that ideal. -/
@[stacks 00IY "annihilation and torsion-by-set criterion"]
theorem isTorsionBySet_iff_smul_top_eq_bot :
    IsTorsionBySet R M m ↔ m • (⊤ : Submodule R M) = ⊥ := sorry

variable [m.IsMaximal]

/-- The length of a module annihilated by a maximal ideal is its rank over the residue field. -/
@[stacks 00IY "length as residue-field rank"]
theorem length_eq_rank_quotient_of_isTorsionBySet
    (hM : IsTorsionBySet R M m) :
    letI := hM.module
    Module.length R M = (Module.rank (R ⧸ m) M).toENat := sorry

/-- For a module annihilated by a maximal ideal, finite length is equivalent to finite
generation over the original ring. -/
@[stacks 00IY "finite length over one residue field"]
theorem isFiniteLength_iff_finite_of_isTorsionBySet
    (hM : IsTorsionBySet R M m) :
    IsFiniteLength R M ↔ Module.Finite R M := sorry

end Module
