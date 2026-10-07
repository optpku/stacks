module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

/-!
# Open Immersions are G-Unramified

An open immersion is G-unramified.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Every open immersion of schemes is G-unramified. -/
instance instGUnramifiedOfIsOpenImmersion [IsOpenImmersion f] : GUnramified f where
  toFormallyUnramified := FormallyUnramified.instOfIsOpenImmersionDiagonalScheme f
  toLocallyOfFinitePresentation := locallyOfFinitePresentation_of_isOpenImmersion f

end AlgebraicGeometry
