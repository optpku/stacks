/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.Algebra.Category.ModuleCat.Flat
import StacksCheckRecall

@[expose] public section

/- Lemma 17.17.2 (05NE): a module sheaf is flat if and only if all of its stalks are flat over
the corresponding stalk rings. -/
@[stacks 05NE]
#check @SheafOfModules.IsFlat.iff_forall_isFlatAt

/- Stalk values are bundled module objects; the generic categorical bridge transports their
algebraic flatness predicate across comparison isomorphisms. -/
#check @ModuleCat.moduleFlat_of_iso
#check @ModuleCat.moduleFlat_iff_of_iso
