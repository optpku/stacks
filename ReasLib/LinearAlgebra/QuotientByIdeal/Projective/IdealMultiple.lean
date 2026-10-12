/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Projective
public import ReasLib.RingTheory.Ideal.Quotient.ReducedCover

/-!
# Ideal multiples in quotients of projective modules

The quotient map by `J • ⊤` restricts to the multiple `I • ⊤`. For a projective module this
restriction is bijective when `I` and `J` have zero intersection.
-/

@[expose] public section

universe u v

namespace Submodule

variable {A : Type u} [CommRing A]
variable {P : Type v} [AddCommGroup P] [Module A P]

/-- The quotient map by `J • ⊤` sends the submodule `I • ⊤` into `I • ⊤` in the quotient
module. -/
theorem smulTopQuotientMap_mem (I J : Ideal A)
    (x : ((I • (⊤ : Submodule A P)) : Submodule A P)) :
    ((J • (⊤ : Submodule A P)).mkQ (x : P)) ∈
      ((I • (⊤ : Submodule A (P ⧸ J • (⊤ : Submodule A P)))) :
        Submodule A (P ⧸ J • (⊤ : Submodule A P))) := sorry

/-- The quotient map by `J • ⊤`, restricted from `I • ⊤` to `I • ⊤` in the quotient
module. -/
def smulTopQuotientMap (I J : Ideal A) :
    ((I • (⊤ : Submodule A P)) : Submodule A P) →ₗ[A]
      ((I • (⊤ : Submodule A (P ⧸ J • (⊤ : Submodule A P)))) :
        Submodule A (P ⧸ J • (⊤ : Submodule A P))) :=
  ((((J • (⊤ : Submodule A P)).mkQ).comp
      (Submodule.subtype ((I • (⊤ : Submodule A P)) : Submodule A P))).codRestrict _
    (smulTopQuotientMap_mem (P := P) I J))

/-- The restricted quotient map agrees with the ordinary quotient map on every element of
`I • ⊤`. -/
theorem smulTopQuotientMap_apply (I J : Ideal A)
    (x : ((I • (⊤ : Submodule A P)) : Submodule A P)) :
    smulTopQuotientMap (P := P) I J x =
      ⟨(J • (⊤ : Submodule A P)).mkQ (x : P), smulTopQuotientMap_mem I J x⟩ := sorry

/-- On a projective module, the restricted quotient map on an ideal multiple is bijective when
the two ideals have zero intersection. -/
theorem smulTopQuotientMap_bijective_of_inf_eq_bot [Module.Projective A P]
    (I J : Ideal A) (hIJ : I ⊓ J = ⊥) :
    Function.Bijective (smulTopQuotientMap (P := P) I J) := sorry

/-- On a projective module over a reduced ring, the restricted quotient map on an ideal multiple
is bijective when the zero loci of the two ideals cover the prime spectrum. -/
theorem smulTopQuotientMap_bijective_of_zeroLocus_union_eq_univ
    [IsReduced A] [Module.Projective A P] (I J : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (I : Set A) ∪
      PrimeSpectrum.zeroLocus (J : Set A) = Set.univ) :
    Function.Bijective (smulTopQuotientMap (P := P) I J) := sorry

end Submodule
