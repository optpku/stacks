module

import StacksCheckRecall
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Quotient

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 37.60.11: for a flat finitely presented ring homomorphism `f : A →+* B` and an ideal
`I : Ideal B`, the composite `A → B ⧸ I` is pseudo-coherent exactly when `I` is pseudo-coherent
as a `B`-module. -/
@[stacks 0697] #check
  (RingHom.IsPseudoCoherentRingMap.quotient_iff_ideal :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      (f : A →+* B) (I : Ideal B) (_ : f.Flat)
      (_ : f.FinitePresentation),
      ((Ideal.Quotient.mk I).comp f).IsPseudoCoherentRingMap ↔
        (ModuleCat.of B I).IsPseudoCoherent)
