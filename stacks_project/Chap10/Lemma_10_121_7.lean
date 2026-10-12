/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Lattice.Distance.Determinant
import StacksCheckRecall

/-!
# Determinants and lattice distance

@stack 02MI

The determinant formula is owned by the neutral ReasLib lattice-distance leaf.
-/

/- Lemma 10.121.7: in the one-dimensional local setting, the lattice distance equals the
additive order of vanishing of the determinant. -/
@[stacks 02MI]
#check @Submodule.latticeDistance_map_eq_log_ordFrac_det

@[stacks 02MI "multiplicative companion"]
#check @Submodule.exp_latticeDistance_map_eq_ordFrac_det
