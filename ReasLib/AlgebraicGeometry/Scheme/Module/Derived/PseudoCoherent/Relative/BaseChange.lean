module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence

/-!
# Base change of relative pseudo-coherence

Tor-independent base change preserves relative pseudo-coherence of derived modules on schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver

/-- Tor-independent base change preserves relative `m`-pseudo-coherence of a derived module
along a locally finite type scheme morphism. -/
theorem pullback {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) {E : RingedSpace.ModuleDerived X.toRingedSpace} {m : ℤ}
    (hE : IsMPseudoCoherentOver f E m)
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g)) :
    IsMPseudoCoherentOver (pullback.snd f g)
      ((RingedSpace.modulePullbackDerived (pullback.fst f g).toShHom).obj E) m := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver
