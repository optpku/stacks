module

public import ReasLib.RingTheory.ReesAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Homogeneous kernel of the Rees quotient map

This file records the canonical ring map `reesAlgebra I →+* reesAlgebra (I.map (Ideal.Quotient.mk p))`
and the homogeneous kernel `P` with `P_d = I ^ d ∩ p`.
-/

@[expose] public section

noncomputable section

universe u

open Polynomial

namespace ReesAlgebra.Grading

variable {A : Type u} [CommRing A]

/-- The canonical Rees algebra map along `Ideal.Quotient.mk p`, sending `reesAlgebra I` to
`reesAlgebra (I.map (Ideal.Quotient.mk p))`. -/
def quotientMap (I p : Ideal A) :
    reesAlgebra I →+* reesAlgebra (I.map (Ideal.Quotient.mk p)) :=
  map (Ideal.Quotient.mk p) Ideal.le_comap_map

/-- The polynomial underlying `quotientMap I p x` is obtained by mapping coefficients along
`Ideal.Quotient.mk p`. -/
theorem quotientMap_apply (I p : Ideal A) (x : reesAlgebra I) :
    (quotientMap I p x).1 = Polynomial.map (Ideal.Quotient.mk p) x.1 := sorry

/-- `quotientMap I p` preserves the degree-`n` Rees piece. -/
theorem quotientMap_mem_grade (I p : Ideal A) {n : ℕ} {x : reesAlgebra I}
    (hx : x ∈ grade I n) :
    quotientMap I p x ∈ grade (I.map (Ideal.Quotient.mk p)) n := sorry

/-- The graded form of `quotientMap I p`. -/
def quotientGradedMap (I p : Ideal A) :
    grade I →+*ᵍ grade (I.map (Ideal.Quotient.mk p)) where
  toRingHom := quotientMap I p
  map_mem := quotientMap_mem_grade I p

/-- The underlying ring homomorphism of `quotientGradedMap I p` is `quotientMap I p`. -/
theorem quotientGradedMap_toRingHom (I p : Ideal A) :
    (quotientGradedMap I p).toRingHom = quotientMap I p := sorry

/-- If `f` is surjective and `J = I.map f`, the induced Rees map is surjective. -/
theorem map_surjective {S : Type u} [CommRing S] {I : Ideal A} {J : Ideal S}
    (f : A →+* S) (hIJ : I ≤ Ideal.comap f J) (hf : Function.Surjective f)
    (hJ : J = I.map f) : Function.Surjective (map f hIJ) := sorry

/-- The homogeneous kernel `P` of `quotientMap I p`, characterized in degree `d` by
`P_d = I ^ d ∩ p`. -/
def strictTransformIdeal (I p : Ideal A) : HomogeneousIdeal (grade I) :=
  HomogeneousIdeal.comap (quotientGradedMap I p) ⊥

/-- Membership in `strictTransformIdeal I p` is coefficientwise membership in `p`. -/
theorem strictTransformIdeal_spec (I p : Ideal A) (x : reesAlgebra I) :
    x ∈ strictTransformIdeal I p ↔ ∀ n, x.1.coeff n ∈ p := sorry

/-- The degree-`n` piece of `strictTransformIdeal I p` is `I ^ n ∩ p`. -/
theorem strictTransformIdeal_grade (I p : Ideal A) (n : ℕ) (a : A) (ha : a ∈ I ^ n) :
    linear I n ⟨a, ha⟩ ∈ strictTransformIdeal I p ↔ a ∈ p := sorry

/-- The underlying ideal of `strictTransformIdeal I p` is the kernel of `quotientMap I p`. -/
theorem strictTransformIdeal_toIdeal (I p : Ideal A) :
    (strictTransformIdeal I p).toIdeal = RingHom.ker (quotientMap I p) := sorry

/-- If `p` is prime, then `strictTransformIdeal I p` is a homogeneous prime ideal. -/
theorem isPrime_toIdeal_strictTransformIdeal (I p : Ideal A) [p.IsPrime] :
    (strictTransformIdeal I p).toIdeal.IsPrime := sorry

/-- If `p` is prime and `¬ I ≤ p`, then `strictTransformIdeal I p` does not contain the
irrelevant ideal. -/
theorem not_irrelevant_le_strictTransformIdeal (I p : Ideal A) [p.IsPrime] (hI : ¬ I ≤ p) :
    ¬ HomogeneousIdeal.irrelevant (grade I) ≤ strictTransformIdeal I p := sorry

/-- The irrelevant ideal of the quotient Rees algebra is contained in the image of the
irrelevant ideal of `reesAlgebra I`. -/
theorem quotientGradedMap_map_irrelevant (I p : Ideal A) :
    HomogeneousIdeal.irrelevant (grade (I.map (Ideal.Quotient.mk p))) ≤
      HomogeneousIdeal.map (quotientGradedMap I p) (HomogeneousIdeal.irrelevant (grade I)) :=
  sorry

end ReesAlgebra.Grading
