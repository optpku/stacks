/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Basic

@[expose] public section

open CategoryTheory

universe u v

namespace RingHom.IsPseudoCoherentRingMap

/-- For a flat finitely presented ring homomorphism `f : A →+* B` and an ideal `I : Ideal B`,
the composite `A → B ⧸ I` is pseudo-coherent exactly when `I` is pseudo-coherent as a
`B`-module. -/
theorem quotient_iff_ideal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal B) (h_flat : f.Flat)
    (h_finitePresentation : f.FinitePresentation) :
    ((Ideal.Quotient.mk I).comp f).IsPseudoCoherentRingMap ↔
      (ModuleCat.of B I).IsPseudoCoherent := sorry

end RingHom.IsPseudoCoherentRingMap
