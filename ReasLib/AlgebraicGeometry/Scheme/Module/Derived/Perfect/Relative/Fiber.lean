module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Bounded.Local
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- For a flat, locally finitely presented morphism `f : X ⟶ S` and a pseudo-coherent
derived `𝒪_X`-module `E`, relative perfectness is equivalent to local boundedness below of
`E` and of its derived pullback to every scheme-theoretic fiber. -/
theorem isPerfectRelativeTo_iff_locallyBoundedBelow_and_fiber {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E) :
    IsPerfectRelativeTo f E ↔
      RingedSpace.ModuleDerived.IsLocallyBoundedBelow E ∧
        ∀ s : S, RingedSpace.ModuleDerived.IsLocallyBoundedBelow
          ((RingedSpace.modulePullbackDerived (f.fiberι s).toShHom).obj E) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
