module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FiniteOrder

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening

/-- A derived module on an algebraic space is pseudo-coherent if its derived pullback
along a finite-order thickening is pseudo-coherent. -/
theorem isPseudoCoherent_of_pullback {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsFiniteOrderThickening i] (K' : ModuleDerived X')
    (hK : IsPseudoCoherent X ((modulePullbackDerived i).obj K')) :
    IsPseudoCoherent X' K' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsFiniteOrderThickening
