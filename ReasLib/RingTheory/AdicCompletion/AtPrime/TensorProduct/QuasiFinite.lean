/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.RingTheory.ZariskisMainTheorem
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AtPrime.TensorProduct

@[expose] public section

/-!
# Quasi-finite completed local tensor products

@stack 07NC

This leaf owns the product splitting of a completed base change at a
quasi-finite prime.  It is stated using the canonical completed-local tensor
map, so applications retain a usable formula for the distinguished projection
instead of only an unstructured existence of a product factor.
-/

open IsLocalRing
open scoped TensorProduct

universe u v

namespace AdicCompletion.AtPrime.TensorProduct

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Stacks Lemma 10.124.3 (tag `07NC`): if an algebra of finite type over a
Noetherian ring is quasi-finite at `q`, then the completed base change at
`q.under R` splits as the completed local ring at `q` times a complementary
factor.  The first projection is the canonical completed-local tensor map. -/
@[stacks 07NC "quasi-finite completed local tensor product splitting"]
theorem exists_prodAlgEquiv_of_quasiFiniteAt
    [Algebra.FiniteType R S] [IsNoetherianRing R]
    (q : Ideal S) [q.IsPrime] [Algebra.QuasiFiniteAt R q] :
    let baseCompletion :=
      AdicCompletion (maximalIdeal (Localization.AtPrime (q.under R)))
        (Localization.AtPrime (q.under R))
    let localCompletion :=
      AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
    letI : Algebra baseCompletion localCompletion :=
      AdicCompletion.AtPrime.Relative.mapAlgebra q
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra baseCompletion B)
      (E : (baseCompletion ⊗[R] S) ≃ₐ[baseCompletion] (localCompletion × B)),
      ∀ z : baseCompletion ⊗[R] S,
        RingHom.fst localCompletion B (E z) = map q (AlgHom.id R S) z := sorry

end AdicCompletion.AtPrime.TensorProduct
