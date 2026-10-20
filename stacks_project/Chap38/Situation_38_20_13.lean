module

public import stacks_project.Chap38.«38_20_13_1_FlatFunctor»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]
variable (T : Over S)

/- Situation 38.20.13: pulling `ℱ` back to `X ×_S T` and testing flatness over `T`
defines a subterminal contravariant functor on schemes over `S`. -/
@[stacks 05MW] #check
  (AlgebraicGeometry.Scheme.Modules.Flattening.functor f ℱ : (Over S)ᵒᵖ ⥤ Type u)

#check Scheme.Modules.Flattening.baseChange f ℱ T

#check Scheme.Modules.Flattening.functor_obj_nonempty_iff f ℱ T

#check Scheme.Modules.Flattening.functor_obj_unique f ℱ T
