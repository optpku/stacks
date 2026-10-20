module

public import ReasLib.RingTheory.RingHom.Perfect.Basic
public import ReasLib.RingTheory.Regular.RingMap

/-!
# Perfect maps from regular rings

This leaf records the finite-dimensional regular-base criterion for perfect
finite type algebra maps.

@stack 067K
-/

@[expose] public section

universe u v

namespace Algebra

/-- Lemma 15.83.5: a finite type algebra over a regular commutative ring of finite Krull
dimension is a perfect ring map. -/
@[stacks 067K "finite type over a finite-dimensional regular ring"]
theorem isPerfectRingMap_of_finiteType_of_isRegularRing_of_finiteDimension
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsRegularRing A] [Algebra.FiniteType A B] (h_finite : ∃ d : ℕ, Ring.KrullDimLE d A) :
    (algebraMap A B).IsPerfectRingMap := sorry
/- Proof strategy: use the Noetherian finite-type instance for pseudo-coherence. Finite-dimensional
regularity bounds the global dimension of `A`, hence gives finite Tor dimension to the `A`-module
`B`; conclude with `RingHom.isPerfectRingMap_iff`. -/

end Algebra
