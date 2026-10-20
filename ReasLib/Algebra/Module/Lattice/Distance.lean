module

public import Mathlib.RingTheory.Length
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Integer distance between submodules

The lattice condition itself is Mathlib's `Submodule.IsLattice`.  This leaf owns only the
integer-valued invariant obtained by comparing the two quotient lengths coming from the
intersection.  Finiteness, locality, and dimension hypotheses belong to the theorems that use
the invariant, not to its definition.
-/

@[expose] public section

universe u v

namespace Submodule

variable {R : Type u} {V : Type v}
variable [CommRing R] [AddCommGroup V] [Module R V]

/-- Definition 10.121.5 (Stacks `02MG`): for two submodules, the distance is the difference of
the lengths of the quotients by their common intersection.  When the submodules are lattices,
this is the lattice distance used in the chapter. -/
@[stacks 02MG]
noncomputable def latticeDistance (M M' : Submodule R V) : ℤ :=
  ((Module.length R (M ⧸ (M ⊓ M').submoduleOf M)).toNat : ℤ) -
    ((Module.length R (M' ⧸ (M ⊓ M').submoduleOf M')).toNat : ℤ)

/-- The defining quotient-length formula for `Submodule.latticeDistance`. -/
@[stacks 02MG "defining formula"]
theorem latticeDistance_def (M M' : Submodule R V) :
    latticeDistance M M' =
      ((Module.length R (M ⧸ (M ⊓ M').submoduleOf M)).toNat : ℤ) -
        ((Module.length R (M' ⧸ (M ⊓ M').submoduleOf M')).toNat : ℤ) := sorry

end Submodule
