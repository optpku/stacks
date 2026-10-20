/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.TrivSqZeroExt
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal

@[expose] public section

universe u v

namespace DividedPowers.TrivSqZeroExt

variable {B : Type u} {M : Type v}
variable [CommRing B] [AddCommGroup M] [Module B M]
variable [Module Bᵐᵒᵖ M] [IsCentralScalar B M]

set_option backward.privateInPublic true in
/-- The zero of the square-zero extension belongs to both coordinate submodules. -/
private theorem submoduleIdeal_zero_mem (J : Ideal B) (N : Submodule B M) :
    (0 : TrivSqZeroExt B M).fst ∈ J ∧ (0 : TrivSqZeroExt B M).snd ∈ N := sorry

set_option backward.privateInPublic true in
/-- Coordinate membership in an ideal and a submodule is closed under addition. -/
private theorem submoduleIdeal_add_mem (J : Ideal B) (N : Submodule B M)
    (first second : TrivSqZeroExt B M)
    (hfirst : first.fst ∈ J ∧ first.snd ∈ N)
    (hsecond : second.fst ∈ J ∧ second.snd ∈ N) :
    (first + second).fst ∈ J ∧ (first + second).snd ∈ N := sorry

set_option backward.privateInPublic true in
/-- Coordinate membership is closed under multiplication when `J` sends `M` into `N`. -/
private theorem submoduleIdeal_smul_mem (J : Ideal B) (N : Submodule B M)
    (hJN : ∀ x ∈ J, ∀ m : M, x • m ∈ N)
    (scalar element : TrivSqZeroExt B M) (helement : element.fst ∈ J ∧ element.snd ∈ N) :
    (scalar • element).fst ∈ J ∧ (scalar • element).snd ∈ N := sorry

set_option backward.privateInPublic true in
/-- The coordinate ideal `J ⊕ N` in the square-zero extension, provided `J • M ⊆ N`. -/
def submoduleIdeal (J : Ideal B) (N : Submodule B M)
    (hJN : ∀ x ∈ J, ∀ m : M, x • m ∈ N) : Ideal (TrivSqZeroExt B M) where
  carrier := {element | element.fst ∈ J ∧ element.snd ∈ N}
  zero_mem' := submoduleIdeal_zero_mem J N
  add_mem' := fun {_ _} hfirst hsecond =>
    submoduleIdeal_add_mem J N _ _ hfirst hsecond
  smul_mem' := fun scalar element helement =>
    submoduleIdeal_smul_mem J N hJN scalar element helement

/-- Membership in the coordinate ideal is simultaneous membership of the two coordinates. -/
theorem mem_submoduleIdeal_iff (J : Ideal B) (N : Submodule B M)
    (hJN : ∀ x ∈ J, ∀ m : M, x • m ∈ N) (element : TrivSqZeroExt B M) :
    element ∈ submoduleIdeal J N hJN ↔ element.fst ∈ J ∧ element.snd ∈ N := sorry

/-- The coordinate ideal `J ⊕ N` is stable under the ambient square-zero divided powers. -/
theorem isSubDPIdeal_submoduleIdeal {J : Ideal B} (δ : DividedPowers J)
    (N : Submodule B M) (hJN : ∀ x ∈ J, ∀ m : M, x • m ∈ N) :
    IsSubDPIdeal (dividedPowers M δ) (submoduleIdeal J N hJN) := sorry

/-- The divided powers on `J ⊕ N` obtained by restricting the square-zero divided powers. -/
noncomputable def submodulePowers {J : Ideal B} (δ : DividedPowers J)
    (N : Submodule B M) (hJN : ∀ x ∈ J, ∀ m : M, x • m ∈ N) :
    DividedPowers (submoduleIdeal J N hJN) :=
  open scoped Classical in
  IsSubDPIdeal.dividedPowers (dividedPowers M δ) (isSubDPIdeal_submoduleIdeal δ N hJN)

/-- On the coordinate ideal, the powers are `(δ.dpow n x, dpowPred δ n x • m)`,
with predecessor power zero at index zero. -/
theorem submodulePowers_apply {J : Ideal B} (δ : DividedPowers J)
    (N : Submodule B M) (hJN : ∀ x ∈ J, ∀ m : M, x • m ∈ N)
    (n : ℕ) (element : TrivSqZeroExt B M) (helement : element ∈ submoduleIdeal J N hJN) :
    submodulePowers δ N hJN n element =
      TrivSqZeroExt.inl (δ.dpow n element.fst) +
        TrivSqZeroExt.inr (dpowPred δ n element.fst • element.snd) := sorry

end DividedPowers.TrivSqZeroExt
