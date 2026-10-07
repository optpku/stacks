module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.WeaklyContractible.Enough
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 7.40.2 (1): an object U of a site C is weakly contractible if the
equivalent conditions of Lemma 7.40.1 hold. -/
@[stacks 090L "(1)"]
#check @CategoryTheory.GrothendieckTopology.IsWeaklyContractible

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Definition 7.40.2 (2): a site has enough weakly contractible objects if every
object U of C has a covering {Uᵢ ⟶ U} with Uᵢ weakly contractible for all i. -/
@[stacks 090L "(2)"]
#check (J.HasEnoughObjectsWithProperty J.IsWeaklyContractible)

#check @CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty.iff_existsWeaklyContractibleCover

/- Definition 7.40.2 (3): more generally, if P is a property of objects of C, the
site has enough P-objects if every object U of C has a covering {Uᵢ ⟶ U} such
that Uᵢ has P for all i. -/
@[stacks 090L "(3)"]
#check @CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty
