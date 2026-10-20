module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Quot
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Representability

/-!
# Representability of the Hilbert functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

/-- The Hilbert functor of a finitely presented separated morphism of algebraic
spaces is represented by an algebraic space locally of finite presentation over
the base. -/
@[stacks 0D01]
theorem hilbert_isLocallyOfFinitePresentationOver {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f] :
    IsLocallyOfFinitePresentationOver (hilbert f) := sorry

/-- The Hilbert functor of a finitely presented separated morphism of algebraic
spaces is represented by an algebraic space over the base. -/
theorem hilbert_isAlgebraicSpaceOver {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [FinitePresentation f] [Separated f] :
    IsAlgebraicSpaceOver (hilbert f) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
