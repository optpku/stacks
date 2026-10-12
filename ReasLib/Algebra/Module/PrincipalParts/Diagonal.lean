/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.Basic
public import ReasLib.LinearAlgebra.TensorProduct.RightModule
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Diagonal-Ideal Presentation of Principal Parts

This leaf presents principal parts as a quotient of `S ⊗[R] M` by powers of
the diagonal ideal.  The tensor-product action is supplied by the scoped
right-factor model; no chapter-specific action or instance is recreated here.

@stack 0H90
-/

@[expose] public section

universe u

noncomputable section

open scoped TensorProduct TensorProduct.Right

namespace PrincipalParts.Diagonal

section

variable {R S M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The `n`th power of the diagonal ideal acting on `S ⊗[R] M`. -/
abbrev powerSubmodule (n : ℕ) : Submodule (S ⊗[R] S) (S ⊗[R] M) :=
  ((KaehlerDifferential.ideal R S) ^ n) •
    (⊤ : Submodule (S ⊗[R] S) (S ⊗[R] M))

/-- The order-`k` diagonal relation, viewed as an `S`-submodule through the left tensor factor. -/
abbrev relation (k : ℕ) : Submodule S (S ⊗[R] M) :=
  Submodule.restrictScalars S
    (powerSubmodule (R := R) (S := S) (M := M) (k + 1))

/-- The diagonal-ideal quotient modelling `PrincipalParts.module R S M k`. -/
abbrev quotient (k : ℕ) : Type u :=
  (S ⊗[R] M) ⧸ relation (R := R) (S := S) (M := M) k

/-- The universal `R`-linear map into the diagonal quotient, `m ↦ [1 ⊗ m]`. -/
def quotientClass (k : ℕ) : M →ₗ[R] quotient (R := R) (S := S) (M := M) k where
  toFun m := (relation (R := R) (S := S) (M := M) k).mkQ ((1 : S) ⊗ₜ[R] m)
  map_add' := sorry
  map_smul' := sorry

/-- The universal quotient-class map has differential-operator order at most `k`. -/
theorem quotientClass.isDifferentialOperatorOfOrder (k : ℕ) :
    (quotientClass (R := R) (S := S) (M := M) k).IsDifferentialOperatorOfOrder S k := sorry

/-- The map from principal parts to its diagonal-ideal quotient presentation. -/
noncomputable def toQuotient (k : ℕ) :
    PrincipalParts.module R S M k →ₗ[S] quotient (R := R) (S := S) (M := M) k :=
  (representingEquiv R S M k (quotient (R := R) (S := S) (M := M) k)).symm
    ⟨quotientClass (R := R) (S := S) (M := M) k,
      quotientClass.isDifferentialOperatorOfOrder (R := R) (S := S) (M := M) k⟩

/-- The forward quotient map sends a universal principal-parts class to `[1 ⊗ m]`. -/
theorem toQuotient.apply_universalDifferential (k : ℕ) (m : M) :
    toQuotient (R := R) (S := S) (M := M) k
        (universalDifferential (R := R) (S := S) (M := M) k m) =
      (relation (R := R) (S := S) (M := M) k).mkQ ((1 : S) ⊗ₜ[R] m) := sorry

/-- The `S`-linear tensor lift `s ⊗ m ↦ s • [m]` into principal parts. -/
abbrev tensorToPrincipalParts (k : ℕ) :
    S ⊗[R] M →ₗ[S] PrincipalParts.module R S M k :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : S →ₗ[S] S).smulRight
      (universalDifferential (R := R) (S := S) (M := M) k))

/-- The tensor lift kills the order-`k` diagonal relation. -/
theorem relation_le_ker (k : ℕ) :
    relation (R := R) (S := S) (M := M) k ≤
      LinearMap.ker (tensorToPrincipalParts (R := R) (S := S) (M := M) k) := sorry

/-- The map from the diagonal quotient back to principal parts. -/
def fromQuotient (k : ℕ) :
    quotient (R := R) (S := S) (M := M) k →ₗ[S]
      PrincipalParts.module R S M k :=
  (relation (R := R) (S := S) (M := M) k).liftQ
    (tensorToPrincipalParts (R := R) (S := S) (M := M) k)
    (relation_le_ker (R := R) (S := S) (M := M) k)

/-- The two maps compose to the identity on the diagonal quotient. -/
theorem toQuotient.comp_fromQuotient (k : ℕ) :
    (toQuotient (R := R) (S := S) (M := M) k).comp
        (fromQuotient (R := R) (S := S) (M := M) k) =
      LinearMap.id := sorry

/-- The two maps compose to the identity on principal parts. -/
theorem fromQuotient.comp_toQuotient (k : ℕ) :
    (fromQuotient (R := R) (S := S) (M := M) k).comp
        (toQuotient (R := R) (S := S) (M := M) k) =
      LinearMap.id := sorry

/-- Chap10 Lemma 10.133.9, tag 0H90: principal parts are canonically the quotient of
`S ⊗[R] M` by the `(k + 1)`st diagonal-ideal power. -/
@[stacks 0H90]
noncomputable def equiv (k : ℕ) :
    PrincipalParts.module R S M k ≃ₗ[S] quotient (R := R) (S := S) (M := M) k :=
  LinearEquiv.ofLinear
    (toQuotient (R := R) (S := S) (M := M) k)
    (fromQuotient (R := R) (S := S) (M := M) k)
    (toQuotient.comp_fromQuotient (R := R) (S := S) (M := M) k)
    (fromQuotient.comp_toQuotient (R := R) (S := S) (M := M) k)

/-- The forward map of the diagonal-quotient equivalence is the canonical map
to the quotient presentation. -/
@[simp, stacks 0H90 "diagonal quotient equivalence forward map"]
theorem equiv_apply (k : ℕ) (x : PrincipalParts.module R S M k) :
    equiv (R := R) (S := S) (M := M) k x =
      toQuotient (R := R) (S := S) (M := M) k x := sorry

/-- The inverse map of the diagonal-quotient equivalence is the canonical map
back to principal parts. -/
@[simp, stacks 0H90 "diagonal quotient equivalence inverse map"]
theorem equiv_symm_apply
    (k : ℕ) (x : quotient (R := R) (S := S) (M := M) k) :
    (equiv (R := R) (S := S) (M := M) k).symm x =
      fromQuotient (R := R) (S := S) (M := M) k x := sorry

/-- Under the diagonal quotient equivalence, the universal class of `m` is `[1 ⊗ m]`. -/
theorem equiv.apply_universalDifferential (k : ℕ) (m : M) :
    equiv (R := R) (S := S) (M := M) k
        (universalDifferential (R := R) (S := S) (M := M) k m) =
      (relation (R := R) (S := S) (M := M) k).mkQ ((1 : S) ⊗ₜ[R] m) := sorry

end

end PrincipalParts.Diagonal

end
