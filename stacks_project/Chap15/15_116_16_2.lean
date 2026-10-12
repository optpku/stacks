/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RootsOfUnity.KummerArtinSchreier.PowerLattice
import StacksCheckRecall

@[expose] public section

/-!
# Equation 15.116.16.2

The congruence is expressed directly as membership in a principal power lattice.  This exposes the
same reusable object used by Equation `15.116.16.1`, while `mem_principal_iff` supplies the source's
coefficient-witness view when a downstream proof needs it.

@stack 09F7
-/

namespace Equation_15_116_16_2

/- Equation 15.116.16.2: the scaled-law correction term is of the predicted order. -/
@[stacks 09F7 "Equation 15.116.16.2: scaled-law power-lattice congruence"]
#check @KummerArtinSchreier.PowerLattice.mulLaw_sub_add_mem

#check @KummerArtinSchreier.PowerLattice.associated_pow_mul_mem
#check @KummerArtinSchreier.PowerLattice.mem_principal_iff

end Equation_15_116_16_2
