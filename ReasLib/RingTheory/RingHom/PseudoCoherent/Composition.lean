/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHomProperties
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.ChangeOfBase

/-!
# Composition of pseudo-coherent ring maps

Pseudo-coherent ring maps are closed under composition.
-/

@[expose] public section

open CategoryTheory

universe u

namespace RingHom.IsPseudoCoherentRingMap

/-- Pseudo-coherent ring maps are stable under composition. -/
theorem stableUnderComposition :
    RingHom.StableUnderComposition (@RingHom.IsPseudoCoherentRingMap) := sorry

/-- The composite of two pseudo-coherent ring maps is pseudo-coherent. -/
instance comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) [f.IsPseudoCoherentRingMap]
    [g.IsPseudoCoherentRingMap] : (g.comp f).IsPseudoCoherentRingMap := sorry

end RingHom.IsPseudoCoherentRingMap
