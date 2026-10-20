module

public import ReasLib.AlgebraicTopology.SimplicialObject.Grp.KanFibration
import StacksCheckRecall

/-!
@stack 08NZ

# Lemma 14.31.6 compatibility facade

The Kan-complex result is a canonical ReasLib instance on the underlying simplicial set of every
simplicial group.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.SimplicialObject.Grp

variable (X : SimplicialObject GrpCat.{u})

/- Lemma 14.31.6: every simplicial group is a Kan complex. -/
@[stacks 08NZ]
#check (SimplicialObject.Grp.underlying.kanComplex X :
  SSet.KanComplex (X ⋙ forget GrpCat))

end CategoryTheory.SimplicialObject.Grp
