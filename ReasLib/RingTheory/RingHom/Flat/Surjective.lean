module

public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Surjective flat ring homomorphisms

The kernel of a surjective flat ring homomorphism is a pure ideal.  Keeping this
at the `RingHom.Flat` layer avoids rebuilding the quotient algebra and its
map-induced scalar structure in every application.
@stack 092M
-/

@[expose] public section

universe u v

namespace RingHom.Flat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The kernel of a surjective flat ring homomorphism is pure. -/
@[stacks 092M "kernel of a surjective flat ring map"]
theorem ker_pure_of_surjective {f : R →+* S} (hflat : f.Flat)
    (hsurj : Function.Surjective f) : (RingHom.ker f).Pure := by
  algebraize [f]
  exact Module.Flat.of_linearEquiv
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId R S) hsurj).toLinearEquiv

end RingHom.Flat
