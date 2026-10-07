module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import StacksCheckRecall

@[expose]
public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Definition 7.52.1: let C be a category and J a Grothendieck topology on C.
A point p of the topology is given by a functor u : C ⥤ Type (Sets) such that
(1) for every covering sieve S on U the map S_p ⟶ (h_U)_p is surjective, and
(2) the stalk functor Sh(C) ⥤ Type, F ↦ F_p, is exact.
The canonical owner is GrothendieckTopology.Point: the functor u is Point.fiber,
covering-sieve surjectivity is Point.jointly_surjective (via (h_U)_p ≅ u(U)),
and F ↦ F_p is Point.sheafFiber. -/
@[stacks 00ZT]
#check GrothendieckTopology.Point.{w} J

variable (p : GrothendieckTopology.Point.{w} J)

#check (p.fiber : C ⥤ Type w)
#check (p.sheafFiber : Sheaf J (Type w) ⥤ Type w)

/- Covering-sieve stalk surjectivity: for every covering sieve S on U, the map
S_p ⟶ (h_U)_p is surjective. -/
@[stacks 00ZT "(1)"]
#check @GrothendieckTopology.Point.jointly_surjective

section
variable [LocallySmall.{w} C]

/- Exactness of the stalk functor Sh(C) ⥤ Type, F ↦ F_p. -/
@[stacks 00ZT "(2)"]
#check (ExactFunctor.of p.sheafFiber : Sheaf J (Type w) ⥤ₑ Type w)

end
