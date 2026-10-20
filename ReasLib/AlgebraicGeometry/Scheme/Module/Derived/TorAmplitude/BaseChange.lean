module

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TorIndependentBaseChange

variable {X' X S' S : Scheme.{u}}

/-- In a Tor-independent cartesian square, derived pullback preserves a fixed
Tor-amplitude interval relative to the base. -/
theorem hasTorAmplitudeInOver
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase f.toShHom))]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules (RingedSpace.Hom.inverseImageBase f'.toShHom))]
    (sq : IsPullback g' f' f g)
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (a b : ℤ)
    (hE : RingedSpace.ModuleDerived.HasTorAmplitudeInOver f.toShHom E a b) :
    RingedSpace.ModuleDerived.HasTorAmplitudeInOver f'.toShHom
      ((RingedSpace.modulePullbackDerived g'.toShHom).obj E) a b := sorry

/-- In a Tor-independent cartesian square, a module flat over the base computes
derived pullback at its degree-zero complex. -/
theorem computesAtSingle
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g)
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
    (𝒢 : X.Modules) (h𝒢 : Scheme.Modules.flatOver 𝒢 f) :
    Functor.LeftDerived.ComputesAt
      (RingedSpace.modulePullbackToDerived g'.toShHom)
      (RingedSpace.ModuleQis X.toRingedSpace)
      ((HomotopyCategory.singleFunctor X.Modules 0).obj 𝒢) := sorry

end AlgebraicGeometry.Scheme.TorIndependentBaseChange
