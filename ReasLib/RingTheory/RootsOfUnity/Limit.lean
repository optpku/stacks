/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import ReasLib.RingTheory.RootsOfUnity.Power

@[expose] public section

universe u

namespace rootsOfUnity

/-- Compatibility for a divisibility-indexed family of roots of unity. -/
def IsCompatibleFamily (κ : Type u) [CommMonoid κ] (S : Set ℕ)
    (ζ : (n : S) → rootsOfUnity n.1 κ) : Prop :=
  ∀ (m n : S) (h : m.1 ∣ n.1), rootsOfUnity.powMap h (ζ n) = ζ m

/-- The compatibility predicate is the defining condition on a roots-of-unity family. -/
theorem isCompatibleFamily_iff (κ : Type u) [CommMonoid κ] (S : Set ℕ)
    (ζ : (n : S) → rootsOfUnity n.1 κ) :
    IsCompatibleFamily κ S ζ ↔
      ∀ (m n : S) (h : m.1 ∣ n.1), rootsOfUnity.powMap h (ζ n) = ζ m := Iff.rfl

/-- The constant identity family is compatible with all roots-of-unity power maps. -/
theorem IsCompatibleFamily.one (κ : Type u) [CommMonoid κ] (S : Set ℕ) :
    IsCompatibleFamily κ S (fun n : S ↦ (1 : rootsOfUnity n.1 κ)) :=
  fun _ _ h ↦ map_one (rootsOfUnity.powMap h)

/-- Pointwise products of compatible roots-of-unity families are compatible. -/
theorem IsCompatibleFamily.mul (κ : Type u) [CommMonoid κ] (S : Set ℕ)
    (ζ ξ : (n : S) → rootsOfUnity n.1 κ)
    (hζ : IsCompatibleFamily κ S ζ) (hξ : IsCompatibleFamily κ S ξ) :
    IsCompatibleFamily κ S (fun n ↦ ζ n * ξ n) :=
  fun m n h ↦
    (map_mul (rootsOfUnity.powMap h) (ζ n) (ξ n)).trans
      (congr_arg₂ (· * ·) (hζ m n h) (hξ m n h))

/-- Pointwise inverses of compatible roots-of-unity families are compatible. -/
theorem IsCompatibleFamily.inv (κ : Type u) [CommMonoid κ] (S : Set ℕ)
    (ζ : (n : S) → rootsOfUnity n.1 κ) (hζ : IsCompatibleFamily κ S ζ) :
    IsCompatibleFamily κ S (fun n ↦ (ζ n)⁻¹) :=
  fun m n h ↦
    (map_inv (rootsOfUnity.powMap h) (ζ n)).trans (congr_arg (·⁻¹) (hζ m n h))

/-- The explicit subgroup of compatible families, modeling the inverse limit of the μₙ. -/
def limit (κ : Type u) [CommMonoid κ] (S : Set ℕ) :
    Subgroup ((n : S) → rootsOfUnity n.1 κ) where
  carrier := {ζ | IsCompatibleFamily κ S ζ}
  one_mem' := fun _ _ h ↦ map_one (rootsOfUnity.powMap h)
  mul_mem' := fun {ζ ξ} hζ hξ m n h ↦
    (map_mul (rootsOfUnity.powMap h) (ζ n) (ξ n)).trans
      (congr_arg₂ (· * ·) (hζ m n h) (hξ m n h))
  inv_mem' := fun {ζ} hζ m n h ↦
    (map_inv (rootsOfUnity.powMap h) (ζ n)).trans (congr_arg (·⁻¹) (hζ m n h))

/-- Membership in the explicit roots-of-unity limit is compatibility of its family. -/
theorem mem_limit_iff (κ : Type u) [CommMonoid κ] (S : Set ℕ)
    (ζ : (n : S) → rootsOfUnity n.1 κ) :
    ζ ∈ limit κ S ↔ IsCompatibleFamily κ S ζ := Iff.rfl

end rootsOfUnity
