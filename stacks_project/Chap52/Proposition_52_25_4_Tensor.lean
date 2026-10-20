module

public import stacks_project.Chap52.«52_25_1_1_EulerCharacteristic»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.CoherentTriple

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {S : CoherentTripleSetup A}

/-- A coherent triple is invertible when both of its module components are tensor-invertible. -/
class IsInvertible (L : CoherentTriple S) : Prop where
  /-- Invertibility of the module on the punctured scheme. -/
  invertible_F : Scheme.Modules.Invertible L.F
  /-- Invertibility of the module on the closed fibre. -/
  invertible_F₀ : Scheme.Modules.Invertible L.F₀

/-- The punctured-scheme component of an invertible coherent triple is invertible. -/
instance IsInvertible.instInvertible_F (L : CoherentTriple S) [hL : L.IsInvertible] :
    Scheme.Modules.Invertible L.F := hL.invertible_F

/-- The closed-fibre component of an invertible coherent triple is invertible. -/
instance IsInvertible.instInvertible_F₀ (L : CoherentTriple S) [hL : L.IsInvertible] :
    Scheme.Modules.Invertible L.F₀ := hL.invertible_F₀

/-- Componentwise invertibility assembles into an invertible coherent triple. -/
instance instIsInvertible_of_components (L : CoherentTriple S)
    [Scheme.Modules.Invertible L.F] [Scheme.Modules.Invertible L.F₀] : L.IsInvertible :=
  { invertible_F := inferInstance
    invertible_F₀ := inferInstance }

end AlgebraicGeometry.CoherentTriple
