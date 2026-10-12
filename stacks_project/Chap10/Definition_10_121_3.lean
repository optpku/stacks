/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Lattice
import StacksCheckRecall

/-!
# Lattices in fraction-field vector spaces

@stack 02ME

Definition 10.121.3 works over a one-dimensional Noetherian local domain `R`,
its fraction field `K`, and a finite-dimensional `K`-vector space `V`.
Mathlib's more general `Submodule.IsLattice K` is the canonical owner: it
stores finite generation over `R` and the condition that the `K`-span is all
of `V`.
-/

@[expose] public section

/- Definition 10.121.3: a lattice is a finite `R`-submodule whose `K`-span is
all of `V`. -/
@[stacks 02ME]
#check @Submodule.IsLattice

@[stacks 02ME "finite-generation field"]
#check @Submodule.IsLattice.fg

@[stacks 02ME "spanning field"]
#check @Submodule.IsLattice.span_eq_top

@[stacks 02ME "finite-generation projection"]
#check @Submodule.IsLattice.finite
