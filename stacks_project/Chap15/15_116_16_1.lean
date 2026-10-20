/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RootsOfUnity.KummerArtinSchreier.DiscreteValuationRing
import StacksCheckRecall

@[expose] public section

/-!
# Equation 15.116.16.1

The reusable statement is the principal-power-lattice membership theorem in
`KummerArtinSchreier.PowerLattice`.  Its premise is written as
`P(z) ∈ π ^ (-n) B`, which is equivalent to the source's finite-level condition
`π ^ n P(z) ∈ B` and avoids the sign inconsistency in the prose equation.

@stack 09F6
-/

namespace Equation_15_116_16_1

/- Equation 15.116.16.1: the quotient-polynomial congruence. -/
@[stacks 09F6 "Equation 15.116.16.1: quotient-polynomial power-lattice congruence"]
#check @KummerArtinSchreier.PowerLattice.aeval_sub_mem

#check @KummerArtinSchreier.PowerLattice.principal
#check @KummerArtinSchreier.PowerLattice.mem_principal_iff

end Equation_15_116_16_1
