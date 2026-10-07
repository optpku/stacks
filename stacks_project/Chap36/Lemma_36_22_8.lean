module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.TorAmplitude.BaseChange
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 36.22.8 (1): in a Tor-independent cartesian square, derived pullback preserves a
fixed Tor-amplitude interval relative to the base. -/
@[stacks 0C0V] #check
  (@AlgebraicGeometry.Scheme.TorIndependentBaseChange.hasTorAmplitudeInOver :
    {X' X S' S : AlgebraicGeometry.Scheme.{u}} →
      (g' : X' ⟶ X) → (f' : X' ⟶ S') → (f : X ⟶ S) → (g : S' ⟶ S) →
      (sq : CategoryTheory.IsPullback g' f' f g) →
      (hTor : AlgebraicGeometry.Scheme.TorIndependentOver
        (CategoryTheory.Over.mk f) (CategoryTheory.Over.mk g)) →
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace) → (a b : ℤ) →
      (hE : AlgebraicGeometry.RingedSpace.ModuleDerived.HasTorAmplitudeInOver
        f.toShHom E a b) →
      AlgebraicGeometry.RingedSpace.ModuleDerived.HasTorAmplitudeInOver f'.toShHom
        ((AlgebraicGeometry.RingedSpace.modulePullbackDerived g'.toShHom).obj E) a b)

/- Lemma 36.22.8 (2): in a Tor-independent cartesian square, a module flat over the base
computes derived pullback at its degree-zero complex. -/
@[stacks 0C0V] #check
  (@AlgebraicGeometry.Scheme.TorIndependentBaseChange.computesAtSingle :
    {X' X S' S : AlgebraicGeometry.Scheme.{u}} →
      (g' : X' ⟶ X) → (f' : X' ⟶ S') → (f : X ⟶ S) → (g : S' ⟶ S) →
      (sq : CategoryTheory.IsPullback g' f' f g) →
      (hTor : AlgebraicGeometry.Scheme.TorIndependentOver
        (CategoryTheory.Over.mk f) (CategoryTheory.Over.mk g)) →
      (𝒢 : X.Modules) → (h𝒢 : AlgebraicGeometry.Scheme.Modules.flatOver 𝒢 f) →
      CategoryTheory.Functor.LeftDerived.ComputesAt
        (AlgebraicGeometry.RingedSpace.modulePullbackToDerived g'.toShHom)
        (AlgebraicGeometry.RingedSpace.ModuleQis X.toRingedSpace)
        ((HomotopyCategory.singleFunctor X.Modules 0).obj 𝒢))
