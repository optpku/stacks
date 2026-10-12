/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
import StacksCheckRecall

@[expose] public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {S : Type u₁} [Category.{v₁} S]
variable {C : Type u₂} [Category.{v₂} C]
variable (p : S ⥤ C) (U : C)
variable {x : S} (hx : p.obj x = U)
variable {V : C} {y z : S} (f : V ⟶ U) (φ : y ⟶ z)

/- `Functor.Fiber` is selected over the extrinsic `HasFibers.Fib`: the source defines the strict
fibre of every functor without any chosen equivalent presentation. Its carrier and
`Functor.Fiber.fiberCategory` use exactly the source's object and morphism subtypes, with
`Functor.IsHomLift` providing the necessary endpoint transports for the equation over the base.
No source hypothesis is generalized; `mk`, `homMk`, `commSq`, and `of_commSq` expose the canonical
constructors and transport-aware views needed by downstream fibre arguments. -/

/- Definition 4.32.2 (1): the fibre category of `p : S ⥤ C` over `U : C` has objects whose image
is `U` and morphisms lying over `𝟙 U`. -/
@[stacks 02XH "fibre objects over a fixed base object"]
#check (Functor.Fiber p U : Type u₁)

@[stacks 02XH "fibre morphisms lying over the identity of the base object"]
#check (Functor.Fiber.fiberCategory (p := p) (S := U) :
  Category.{v₁} (Functor.Fiber p U))

/- Companion recall: `Functor.Fiber.homMk` constructs a fibre morphism from a morphism in `S`
lying over `𝟙 U`. -/
#check Functor.Fiber.homMk

/- Definition 4.32.2 (2): a lift of `U : C` is an object `x : S` equipped with
`p.obj x = U`, hence an object of `Functor.Fiber p U`. -/
@[stacks 02XH "object lifts as objects of the corresponding fibre"]
#check (Functor.Fiber.mk hx : Functor.Fiber p U)

/- Definition 4.32.2 (3): a lift of `f : V ⟶ U` is a morphism `φ : y ⟶ x` in `S` lying over
`f`, represented by the endpoint-aware predicate `Functor.IsHomLift p f φ`. -/
@[stacks 02XH "morphism lifts lying over a prescribed base morphism"]
#check (Functor.IsHomLift p f φ : Prop)

/- Companion recall: from a hom lift one canonically gets the textbook commutative square
after transporting source and target along the induced equalities. -/
#check IsHomLift.commSq

/- Companion recall: conversely, the textbook commutative square yields the canonical hom-lift
predicate via `IsHomLift.of_commSq`. -/
#check IsHomLift.of_commSq

end CategoryTheory
