/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Quotients of graded Rees algebras

The quotient of a ring by an ideal induces a graded map of Rees algebras.
Its homogeneous kernel is characterized coefficientwise.
-/

@[expose] public section

noncomputable section

universe u

open Polynomial

namespace ReesAlgebra.Grading

variable {A : Type u} [CommRing A]

/-- The Rees algebra map along `Ideal.Quotient.mk p`. -/
def quotientMap (I p : Ideal A) :
    reesAlgebra I →+* reesAlgebra (I.map (Ideal.Quotient.mk p)) :=
  map (Ideal.Quotient.mk p) Ideal.le_comap_map

/-- Mapping a Rees polynomial to the quotient maps its coefficients. -/
theorem quotientMap_apply (I p : Ideal A) (x : reesAlgebra I) :
    (quotientMap I p x).1 = Polynomial.map (Ideal.Quotient.mk p) x.1 := sorry

/-- The quotient map preserves each graded Rees piece. -/
theorem quotientMap_mem_grade (I p : Ideal A) {n : ℕ} {x : reesAlgebra I}
    (hx : x ∈ grade I n) :
    quotientMap I p x ∈ grade (I.map (Ideal.Quotient.mk p)) n := sorry

/-- The graded Rees algebra map induced by quotienting the base ring. -/
def quotientGradedMap (I p : Ideal A) :
    grade I →+*ᵍ grade (I.map (Ideal.Quotient.mk p)) where
  toRingHom := quotientMap I p
  map_mem := quotientMap_mem_grade I p

/-- The underlying ring map of the graded quotient map. -/
theorem quotientGradedMap_toRingHom (I p : Ideal A) :
    (quotientGradedMap I p).toRingHom = quotientMap I p := sorry

/-- A surjection of base rings induces a surjection of Rees algebras when the
target ideal is the image of the source ideal. -/
theorem map_surjective {S : Type u} [CommRing S] {I : Ideal A} {J : Ideal S}
    (f : A →+* S) (hIJ : I ≤ Ideal.comap f J) (hf : Function.Surjective f)
    (hJ : J = I.map f) : Function.Surjective (map f hIJ) := sorry

/-- The homogeneous kernel of the graded Rees quotient map. -/
def strictTransformIdeal (I p : Ideal A) : HomogeneousIdeal (grade I) :=
  HomogeneousIdeal.comap (quotientGradedMap I p) ⊥

/-- Membership in the homogeneous kernel is coefficientwise membership in `p`. -/
theorem strictTransformIdeal_spec (I p : Ideal A) (x : reesAlgebra I) :
    x ∈ strictTransformIdeal I p ↔ ∀ n, x.1.coeff n ∈ p := sorry

/-- The degree-`n` piece of the homogeneous kernel has coefficients in `I ^ n ∩ p`. -/
theorem strictTransformIdeal_grade (I p : Ideal A) (n : ℕ) (a : A) (ha : a ∈ I ^ n) :
    linear I n ⟨a, ha⟩ ∈ strictTransformIdeal I p ↔ a ∈ p := sorry

/-- The ideal underlying the homogeneous kernel equals the ring-map kernel. -/
theorem strictTransformIdeal_toIdeal (I p : Ideal A) :
    (strictTransformIdeal I p).toIdeal = RingHom.ker (quotientMap I p) := sorry

/-- Quotienting by a prime ideal gives a prime homogeneous kernel. -/
theorem isPrime_toIdeal_strictTransformIdeal (I p : Ideal A) [p.IsPrime] :
    (strictTransformIdeal I p).toIdeal.IsPrime := sorry

/-- If the center is not contained in `p`, the homogeneous kernel does not
contain the irrelevant ideal. -/
theorem not_irrelevant_le_strictTransformIdeal (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    ¬ HomogeneousIdeal.irrelevant (grade I) ≤ strictTransformIdeal I p := sorry

/-- The image of the irrelevant ideal contains the irrelevant ideal of the
quotient Rees algebra. -/
theorem quotientGradedMap_map_irrelevant (I p : Ideal A) :
    HomogeneousIdeal.irrelevant (grade (I.map (Ideal.Quotient.mk p))) ≤
      HomogeneousIdeal.map (quotientGradedMap I p) (HomogeneousIdeal.irrelevant (grade I)) :=
  sorry

/-- The Rees quotient map is surjective. -/
theorem quotientMap_surjective (I p : Ideal A) :
    Function.Surjective (quotientMap I p) := sorry

end ReesAlgebra.Grading
