/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.BaseChange
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Formally Étale Base Change for Principal Parts

@stack 0H94

This leaf records the principal-parts comparison under a formally étale scalar
extension.  The comparison map itself is the generic
`PrincipalParts.BaseChange.map` followed by ordinary scalar extension; no
second source-specific map owner is introduced.
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace PrincipalParts.BaseChange.FormallyEtale

section BaseChange

variable {R S S' M : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- Chap10 Lemma 10.150.8 (1), tag 0H94: the principal-parts comparison induced by
`M → S' ⊗[S] M` realizes the target as scalar extension along a formally étale map `S → S'`. -/
@[stacks 0H94]
theorem isBaseChange [Algebra.FormallyEtale S S'] (k : ℕ) :
    IsBaseChange S'
      (BaseChange.map (A := R) (B := S) (A' := R) (B' := S') (M := M)
        (M' := S' ⊗[S] M) k (TensorProduct.mk S S' M 1)) := sorry

/-- The formally etale principal-parts comparison as a linear equivalence after scalar
extension. -/
@[stacks 0H94 "formally etale principal-parts equivalence"]
noncomputable def equiv [Algebra.FormallyEtale S S'] (k : ℕ) :
    S' ⊗[S] PrincipalParts.module R S M k ≃ₗ[S']
      PrincipalParts.module R S' (S' ⊗[S] M) k :=
  (isBaseChange (R := R) (S := S) (S' := S') (M := M) k).equiv

/-- The forward map of `equiv` is the scalar-extension lift of the principal-parts comparison. -/
@[simp, stacks 0H94 "formally etale principal-parts equivalence forward map"]
theorem equiv_toLinearMap [Algebra.FormallyEtale S S'] (k : ℕ) :
    (equiv (R := R) (S := S) (S' := S') (M := M) k).toLinearMap =
      (BaseChange.map (A := R) (B := S) (A' := R) (B' := S') (M := M)
        (M' := S' ⊗[S] M) k (TensorProduct.mk S S' M 1)).liftBaseChange S' := sorry

end BaseChange

end PrincipalParts.BaseChange.FormallyEtale
