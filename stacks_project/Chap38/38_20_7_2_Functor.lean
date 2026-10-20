module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.FreeAtGenericPoints

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (p : ℕ)
variable [Smooth f] [GeometricallyIrreducible f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

#check (Scheme.Flattening.freeAtGenericPointsFunctor f ℱ p : (Over S)ᵒᵖ ⥤ Type u)

end AlgebraicGeometry
