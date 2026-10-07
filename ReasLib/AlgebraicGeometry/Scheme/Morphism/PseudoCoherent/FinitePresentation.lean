module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import ReasLib.RingTheory.RingHom.PseudoCoherent.FinitePresentation

/-!
# Finite presentation of pseudo-coherent morphisms

Pseudo-coherent morphisms of schemes are locally of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PseudoCoherent

/-- A pseudo-coherent morphism of schemes is locally of finite presentation. -/
instance locallyOfFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y) [PseudoCoherent f] :
    LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry.PseudoCoherent
