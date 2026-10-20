module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import ReasLib.RingTheory.RingHom.PseudoCoherent.BaseChange

/-!
# Flat base change of pseudo-coherent scheme morphisms

Pseudo-coherent morphisms of schemes are preserved by base change along flat morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PseudoCoherent

/-- Pseudo-coherent scheme morphisms are stable under base change along a fixed flat
morphism. -/
instance instIsStableUnderBaseChangeAlong {S' S : Scheme.{u}} (g : S' ⟶ S) [Flat g] :
    MorphismProperty.IsStableUnderBaseChangeAlong (@PseudoCoherent.{u}) g := sorry

/-- The second projection from the pullback of a pseudo-coherent morphism along a flat morphism
is pseudo-coherent. -/
instance pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [PseudoCoherent f] [Flat g] : PseudoCoherent (pullback.snd f g) := sorry

end AlgebraicGeometry.PseudoCoherent
