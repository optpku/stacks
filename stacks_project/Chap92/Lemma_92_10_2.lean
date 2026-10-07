module

public import stacks_project.Chap92.Lemma_92_3_4_DirectLimit
public import ReasLib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Tactic.CrossRefAttribute

/-!
# Frobenius functoriality of the cotangent complex

In characteristic `p`, the Section 92.6 map of `L_{B/A}` induced by the Frobenius
endomorphisms of `A` and `B` is chain-homotopic to zero.
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex

universe u

noncomputable section

namespace Algebra.CotangentComplex.Frobenius

/-- The prime `p` vanishes in the codomain of a ring map from a ring in which `p`
vanishes. -/
theorem prime_eq_zero (p : ℕ) [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hp : (p : A) = 0) : (p : B) = 0 :=
  sorry

/-- The Frobenius endomorphisms of `A` and `B` form a commutative square with `f`. -/
theorem w (p : ℕ) [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hp : (p : A) = 0) :
    f.comp (RingHom.frobeniusOfPrime p hp) =
      (RingHom.frobeniusOfPrime p (prime_eq_zero p f hp)).comp f :=
  sorry

/-- The map of cotangent complexes `L_{B/A} ⟶ L_{B/A}` induced by the Frobenius
endomorphisms of `A` and `B`. -/
def map (p : ℕ) [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hp : (p : A) = 0) :
    ((ModuleCat.extendScalars
        (RingHom.frobeniusOfPrime p (prime_eq_zero p f hp))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (RingHom.cotangentComplex f) ⟶
    RingHom.cotangentComplex f :=
  Algebra.CotangentComplex.map f f (RingHom.frobeniusOfPrime p hp)
    (RingHom.frobeniusOfPrime p (prime_eq_zero p f hp)) (w p f hp)

/-- Unfolding of `map` as the functoriality map of the Frobenius square. -/
theorem map_eq (p : ℕ) [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hp : (p : A) = 0) :
    map p f hp =
      Algebra.CotangentComplex.map f f (RingHom.frobeniusOfPrime p hp)
        (RingHom.frobeniusOfPrime p (prime_eq_zero p f hp)) (w p f hp) :=
  sorry

/-- Lemma 92.10.2. Let `p` be a prime number. Let `A ⟶ B` be a ring homomorphism and
assume that `p = 0` in `A`. The map `L_{B/A} ⟶ L_{B/A}` of Section 92.6 induced by
the Frobenius maps `F_A` and `F_B` is homotopic to zero. -/
@[stacks 0G5Z]
theorem map_homotopic_zero (p : ℕ) [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hp : (p : A) = 0) :
    Nonempty (Homotopy (map p f hp) 0) :=
  sorry

end Algebra.CotangentComplex.Frobenius

