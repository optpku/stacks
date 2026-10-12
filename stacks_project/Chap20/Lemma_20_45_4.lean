/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Gluing.OpenFamily.Uniqueness

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing

/-
Lemma 20.45.4: under the covering, overlap-generation, and local negative self-Ext hypotheses,
two bundled realizations are uniquely compatibly isomorphic, and every realized ambient object
has vanishing negative self-Ext.  Bundling each realization removes four parallel public inputs.
-/

@[stacks 0D68 "Lemma 20.45.4 (1): uniqueness of open-family derived realizations"]
#check @OpenFamily.existsUniqueIso

@[stacks 0D68 "Lemma 20.45.4 (2): negative self-Ext vanishing for a realization"]
#check @OpenFamily.negativeSelfExtIsZero

@[stacks 0D68 "open-family overlap generation"]
#check @OpenFamily.GeneratesOverlaps

end
