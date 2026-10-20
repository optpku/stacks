module

public import ReasLib.Algebra.Module.Lattice.Distance.Properties
import StacksCheckRecall

/-!
# Additivity of lattice distance

@stack 02MH
-/

@[expose] public section

-- Lemma 10.121.6 (1): lattice distance is additive on three lattices over a
-- one-dimensional Noetherian local domain.  The owner uses the stronger reusable
-- `KrullDim ≤ 1` hypothesis.
@[stacks 02MH "(1), additivity"]
#check @Submodule.latticeDistance_add

-- Lemma 10.121.6 (2): swapping two lattices negates their distance.
@[stacks 02MH "(2), skew-symmetry"]
#check @Submodule.latticeDistance_neg_swap
