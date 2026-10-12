/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import ReasLib.CategoryTheory.Monoidal.Flat.Exact
import StacksCheckRecall

/-!
# Lemma 17.20.4

The exactness theorem is owned for arbitrary morphisms of ringed spaces in ReasLib.  Its functor
is the canonical pullback followed by the ambient tensor-right functor.
-/

@[expose] public section

/- Lemma 17.20.4: pullback followed by tensoring with a module flat over the target is exact. -/
@[stacks 0GMU]
#check @SheafOfModules.IsFlatOver.exactPullbackTensor

/- The theorem form and the generic ringed-site exact functor remain directly available. -/
#check @SheafOfModules.IsFlatOver.pullbackTensorExact
#check @SheafOfModules.RingedSite.IsFlatOver.exactPullbackTensor

/- Braiding supplies the symmetric left-tensor form without rebuilding a second exactness API. -/
#check @CategoryTheory.MonoidalCategory.shortExact_map_tensorLeft_of_flat_quotient
