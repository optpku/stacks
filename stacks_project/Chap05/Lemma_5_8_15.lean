/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.IrreducibleComponents.Maps
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.8.15

The irreducible-fiber specialization of Mathlib's component correspondence is owned by
`ReasLib.Topology.IrreducibleComponents.Maps`.
-/

/- Lemma 5.8.15: open continuous maps with irreducible fibers identify irreducible components. -/
@[stacks 037A]
#check @irreducibleComponentsEquivOfIrreducibleFibers

/- The source-side component corresponding to a target component is the inverse image. -/
#check @coe_irreducibleComponentsEquivOfIrreducibleFibers_apply

/- The inverse component correspondence sends a source component to its image. -/
#check @coe_irreducibleComponentsEquivOfIrreducibleFibers_symm_apply
