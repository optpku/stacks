/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Cancellation

/-!
# Cancellation for pseudo-coherent morphisms of schemes

Pseudo-coherence of scheme morphisms satisfies cancellation along a pseudo-coherent morphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.PseudoCoherent

/-- If a scheme morphism and its composite with a second morphism are pseudo-coherent, then
the first morphism is pseudo-coherent. -/
theorem of_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [PseudoCoherent g] [PseudoCoherent (f ≫ g)] :
    PseudoCoherent f := sorry

end AlgebraicGeometry.PseudoCoherent
