/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Lattice.Length
import StacksCheckRecall

/-!
# Lattices over one-dimensional Noetherian local domains

@stack 02MF
-/

@[expose] public section

/- Lemma 10.121.4 (1): the over-lattice, finite-length, and finite-module conditions are
equivalent. -/
@[stacks 02MF "(1)"]
#check @Submodule.IsLattice.tfae_of_le

/- Lemma 10.121.4 (2): a submodule is a lattice exactly when its quotient has finite length. -/
@[stacks 02MF "(2)"]
#check @Submodule.IsLattice.iff_length_lt_top_of_le

/- Lemma 10.121.4 (3): intersections and sums of lattices are lattices. -/
@[stacks 02MF "(3), intersection"]
#check @Submodule.IsLattice.inf_of_isNoetherianRing

@[stacks 02MF "(3), sum"]
#check @Submodule.IsLattice.sup

/- Lemma 10.121.4 (4): quotient length is additive along a chain of lattices. -/
@[stacks 02MF "(4)"]
#check @Submodule.length_quotient_eq_add_of_lattice_chain

/- Lemma 10.121.4 (5): the common length difference may be computed using any lower lattice, the
intersection and sum, or any upper lattice. -/
@[stacks 02MF "(5), lower lattice"]
#check @Submodule.length_difference_inf_eq_length_difference_of_le_inf

@[stacks 02MF "(5), intersection and sum"]
#check @Submodule.length_difference_inf_eq_length_difference_sup

@[stacks 02MF "(5), upper lattice"]
#check @Submodule.length_difference_sup_eq_length_difference_of_sup_le
