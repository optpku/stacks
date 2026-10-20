module

public import ReasLib.Topology.Category.TopCommRingCat.Colimits
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

/- Lemma 5.30.9: colimits and their algebraic forgetful-functor compatibility belong to the
canonical owner `TopCommRingCat`. -/
@[stacks 0B24 "topological commutative rings have colimits"]
#check (inferInstance : HasColimits TopCommRingCat.{u})

@[stacks 0B24 "colimits are preserved by the forgetful functor to commutative rings"]
#check (inferInstance : PreservesColimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}))
