module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsFiniteOrderThickening

/-- If the derived pullback of a complex along a finite-order thickening is pseudo-coherent,
then the original complex is pseudo-coherent. -/
theorem isPseudoCoherent_of_pullback {X X' : Scheme.{u}} (i : X ⟶ X')
    [IsFiniteOrderThickening i]
    (K' : RingedSpace.ModuleDerived X'.toRingedSpace)
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent
      ((RingedSpace.modulePullbackDerived i.toShHom).obj K')) :
    RingedSpace.ModuleDerived.IsPseudoCoherent K' := sorry

end AlgebraicGeometry.IsFiniteOrderThickening
