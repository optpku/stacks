/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Chinese remainder interfaces for finite ideal families

For a finite pairwise-comaximal family of ideals, the product equals the
intersection, and the quotient by this product is equivalent to the product
of the individual quotients.
-/

@[expose] public section

universe u v

namespace Ideal.ChineseRemainder

open Function
open Ideal
open scoped BigOperators

section Product

variable {R : Type u} [CommSemiring R]
variable {ι : Type v} [Fintype ι]

/-- A finite pairwise-comaximal family of ideals has equal product and infimum. -/
@[stacks 00DT "finite pairwise-comaximal ideal product"]
theorem prod_eq_iInf (I : ι → Ideal R)
    (hI : Pairwise (IsCoprime on I)) :
    ∏ i, I i = ⨅ i, I i := sorry

end Product

section Quotient

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι]

/-- Quotienting by the product of a finite pairwise-comaximal family of ideals
is equivalent to the product of its quotients. -/
@[stacks 00DT "finite Chinese remainder quotient equivalence"]
noncomputable def quotientProdEquiv (I : ι → Ideal R)
    (hI : Pairwise (IsCoprime on I)) :
    R ⧸ ∏ i, I i ≃+* ∀ i, R ⧸ I i :=
  (Ideal.quotEquivOfEq
      (Eq.trans
        (Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := (Finset.univ : Finset ι))
          (fun _ _ _ _ hij => hI hij))
        ((Finset.inf_eq_iInf (Finset.univ : Finset ι) I).symm.trans
          (Finset.inf_univ_eq_iInf I)))).trans
    (Ideal.quotientInfRingEquivPiQuotient I hI)

/-- The product-form Chinese remainder equivalence sends a quotient class to
the tuple of its coordinate quotient classes. -/
@[stacks 00DT "finite Chinese remainder quotient evaluation", simp]
theorem quotientProdEquiv_apply_mk (I : ι → Ideal R)
    (hI : Pairwise (IsCoprime on I)) (x : R) :
    quotientProdEquiv I hI (Ideal.Quotient.mk (∏ i, I i) x) =
      fun i ↦ Ideal.Quotient.mk (I i) x := sorry

end Quotient

end Ideal.ChineseRemainder
