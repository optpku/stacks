module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.FreeAtGenericPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (p : ℕ)
variable [Smooth f] [GeometricallyIrreducible f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/- 38.20.7.2: the subterminal functor `H_p` records whether the base-changed module is free of
rank `p` near the generic point of every fibre. -/
@[stacks 05MR] #check
  (AlgebraicGeometry.Scheme.Flattening.freeAtGenericPointsFunctor f ℱ p :
    (Over S)ᵒᵖ ⥤ Type u)

end AlgebraicGeometry
