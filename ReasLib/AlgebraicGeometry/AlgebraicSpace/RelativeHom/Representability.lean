module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.MorphismFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Representability
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Representability of the relative-Hom functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- If `x : X ⟶ B` is finitely presented and separated and `z : Z ⟶ B` is
finitely presented, flat, and proper, then the relative-Hom functor `mor z x`
is represented by an algebraic space locally of finite presentation over `B`. -/
@[stacks 0D1C]
theorem mor_isLocallyOfFinitePresentationOver {S : Scheme.{u}}
    {Z B X : AlgebraicSpace S} (z : Z ⟶ B) (x : X ⟶ B)
    [FinitePresentation x] [Separated x] [FinitePresentation z] [Flat z]
    [Proper z] : IsLocallyOfFinitePresentationOver (mor z x) := sorry

/-- If `x : X ⟶ B` is finitely presented and separated and `z : Z ⟶ B` is
finitely presented, flat, and proper, then `mor z x` is represented by an
algebraic space over `B`. -/
theorem mor_isAlgebraicSpaceOver {S : Scheme.{u}} {Z B X : AlgebraicSpace S}
    (z : Z ⟶ B) (x : X ⟶ B) [FinitePresentation x] [Separated x]
    [FinitePresentation z] [Flat z] [Proper z] :
    IsAlgebraicSpaceOver (mor z x) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
