module

public import stacks_project.Chap38.«38_20_3_2_FlatFunctor»
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

variable (A : Type u) (B : Type v) (M : Type w)
variable [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [AddCommGroup M] [Module B M]

/- Situation 38.20.3: local algebras and the closed-point flatness condition
define a subterminal functor on local `A`-algebras. -/
@[stacks 05MK] #check
  (LocalAlgCat.Flattening.functor A B M : LocalAlgCat.{v} A ⥤ Type u)
