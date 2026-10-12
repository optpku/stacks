/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Cohomology.FiniteFreeLocus
import StacksCheckRecall

@[expose] public section

/- Lemma 20.49.11 (1): for a perfect derived module over a ringed space with local stalk rings,
the locus where every cohomology stalk is finite free is open. -/
@[stacks 0GT1 "(1)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.isOpen_finiteFreeLocus

/- Lemma 20.49.11 (2): this locus is the maximal open subset on which every cohomology sheaf is
finite locally free. -/
@[stacks 0GT1 "(2)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.finiteLocallyFreeOn_iff_le_finiteFreeOpen
