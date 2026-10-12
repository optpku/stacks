/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth

/-!
# Standard smoothness criterion for étale ring homomorphisms
-/

@[expose] public section

universe u

namespace RingHom

/-- A commutative ring homomorphism is étale exactly when it is standard smooth of relative
dimension zero. -/
theorem etale_iff_standardSmooth_zero {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    f.Etale ↔ RingHom.IsStandardSmoothOfRelativeDimension 0 f := sorry

end RingHom
