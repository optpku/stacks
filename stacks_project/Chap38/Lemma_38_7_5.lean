/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.Quotient
import StacksCheckRecall

@[expose] public section

universe u v w z

/- Lemma 38.7.5: over a commutative local ring, a linear map from a projective module
to a flat module is universally injective if its reduction modulo the maximal ideal is
injective. -/
@[stacks 05FQ] #check
  (LinearMap.universallyInjective_of_projective_of_injective_mod_maximalIdeal :
    ∀ {R : Type u} {M : Type v} {N : Type w}
      [CommRing R] [IsLocalRing R]
      [AddCommGroup M] [Module R M] [Module.Projective R M]
      [AddCommGroup N] [Module R N] [Module.Flat R N]
      (f : M →ₗ[R] N)
      (_ : Function.Injective
        (f.quotientMapByIdeal (IsLocalRing.maximalIdeal R))),
      LinearMap.UniversallyInjective.{u, v, w, z} f)
