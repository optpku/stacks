/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.Functorial
public import ReasLib.Algebra.Module.PrincipalParts.BaseChange

/-!
# Truncation maps for principal parts

The universal differential of order `k` is also a differential operator of every larger order.
The representing property of principal parts therefore gives canonical transition maps from
`PrincipalParts.module R S M l` to `PrincipalParts.module R S M k` for `k ≤ l`. This file records
their functoriality in the module, transitivity in the order bound, and compatibility with change
of rings.

@stack 09CL
-/

@[expose] public section

universe u

noncomputable section

namespace PrincipalParts

section FixedAlgebra

variable {R S M N : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- The universal differential into `k`-th principal parts has every order bound `l ≥ k`. -/
theorem universalDifferential_mono {k l : ℕ} (h : k ≤ l) :
    (universalDifferential (R := R) (S := S) (M := M) k).IsDifferentialOperatorOfOrder S l :=
  sorry

/-- Tag 09CL: the canonical truncation map from `PrincipalParts.module R S M l` to
`PrincipalParts.module R S M k` for `k ≤ l`. -/
@[stacks 09CL "order truncation"]
noncomputable def truncate {k l : ℕ} (h : k ≤ l) :
    PrincipalParts.module R S M l →ₗ[S] PrincipalParts.module R S M k :=
  (representingEquiv R S M l (PrincipalParts.module R S M k)).symm
    ⟨universalDifferential (R := R) (S := S) (M := M) k,
      universalDifferential_mono (R := R) (S := S) (M := M) h⟩

/-- Truncation sends the universal class of order `l` to the universal class of order `k`. -/
@[simp]
theorem truncate_apply_universalDifferential {k l : ℕ} (h : k ≤ l) (m : M) :
    truncate (R := R) (S := S) (M := M) h
        (universalDifferential (R := R) (S := S) (M := M) l m) =
      universalDifferential (R := R) (S := S) (M := M) k m := sorry

/-- Truncation along a reflexive order comparison is the identity. -/
@[simp]
theorem truncate_refl (k : ℕ) :
    truncate (R := R) (S := S) (M := M) (le_refl k) = LinearMap.id := sorry

/-- Successive truncations agree with truncation along the composite order comparison. -/
@[simp]
theorem truncate_trans {k l n : ℕ} (hkl : k ≤ l) (hln : l ≤ n) :
    (truncate (R := R) (S := S) (M := M) hkl).comp
        (truncate (R := R) (S := S) (M := M) hln) =
      truncate (R := R) (S := S) (M := M) (hkl.trans hln) := sorry

/-- Every principal-parts truncation map is surjective. -/
theorem truncate_surjective {k l : ℕ} (h : k ≤ l) :
    Function.Surjective (truncate (R := R) (S := S) (M := M) h) := sorry

variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- Principal-parts truncation is natural in the module argument. -/
theorem truncate_naturality {k l : ℕ} (h : k ≤ l) (f : M →ₗ[S] N) :
    (truncate (R := R) (S := S) (M := N) h).comp
        (map (R := R) (S := S) l f) =
      (map (R := R) (S := S) k f).comp
        (truncate (R := R) (S := S) (M := M) h) := sorry

end FixedAlgebra

section BaseChange

variable {A B A' B' M M' : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra A' B'] [Algebra B B']
variable [IsScalarTower A B B'] [IsScalarTower A A' B']
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup M'] [Module B' M'] [Module A M'] [Module A' M'] [Module B M']
variable [IsScalarTower A' B' M'] [IsScalarTower B B' M'] [IsScalarTower A A' M']

/-- Principal-parts truncation commutes with the canonical base-change map. -/
theorem truncate_baseChange {k l : ℕ} (h : k ≤ l) (f : M →ₗ[B] M') :
    ((truncate (R := A') (S := B') (M := M') h).restrictScalars B).comp
        (BaseChange.map (A := A) (B := B) (A' := A') (B' := B')
          (M := M) (M' := M') l f) =
      (BaseChange.map (A := A) (B := B) (A' := A') (B' := B')
        (M := M) (M' := M') k f).comp
          (truncate (R := A) (S := B) (M := M) h) := sorry

end BaseChange

end PrincipalParts
