/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derivations of naturally graded monoid objects

A predifferential on a naturally graded object lowers positive degrees by one.  This file records
the categorical graded Leibniz rule without choosing an ambient module category or a particular
graded algebra.  The three clauses are the positive-positive, positive-zero, and zero-positive
parts of the rule; together they are exactly what is needed for a multiplication map of
nonnegatively graded complexes.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

universe u v w

namespace CategoryTheory.GradedObject

variable {C : Type u} [Category.{v} C]
variable {I : Type w}

/-- Transport between equal components of a graded object. -/
@[stacks 062K "transport between equal graded components"]
def reindex (A : GradedObject I C) {i j : I} (h : i = j) : A i ⟶ A j :=
  eqToHom (congrArg A h)

/-- A predifferential on a naturally graded object lowers every positive degree by one. -/
@[stacks 062K "predifferential on a naturally graded object"]
abbrev Predifferential (A : GradedObject ℕ C) :=
  ∀ n : ℕ, A (n + 1) ⟶ A n

namespace Monoidal

variable [MonoidalCategory C] [Preadditive C]

/-- The categorical graded Leibniz rule for a predifferential on a naturally graded object. -/
@[stacks 062K "derivation of a naturally graded monoid object"]
structure IsDerivation (A : GradedObject ℕ C)
    (mul : ∀ n m : ℕ, A n ⊗ A m ⟶ A (n + m))
    (d : A.Predifferential) : Prop where
  /-- Leibniz rule when both homogeneous inputs have positive degree. -/
  mul_succ_succ (n m : ℕ) :
    mul (n + 1) (m + 1) ≫
          A.reindex
            ((Nat.succ_add n (m + 1)).trans
              (congrArg Nat.succ (Nat.add_succ n m))) ≫
          d (n + m + 1) =
      (d n ▷ A (m + 1)) ≫ mul n (m + 1) ≫
          A.reindex (Nat.add_succ n m) +
        ((-1 : ℤ) ^ (n + 1)) •
          ((A (n + 1) ◁ d m) ≫ mul (n + 1) m ≫
            A.reindex (Nat.succ_add n m))
  /-- Leibniz rule when the right homogeneous input has degree zero. -/
  mul_succ_zero (n : ℕ) :
    mul (n + 1) 0 ≫ A.reindex (Nat.add_zero (n + 1)) ≫ d n =
      (d n ▷ A 0) ≫ mul n 0 ≫ A.reindex (Nat.add_zero n)
  /-- Leibniz rule when the left homogeneous input has degree zero. -/
  mul_zero_succ (m : ℕ) :
    mul 0 (m + 1) ≫ A.reindex (Nat.zero_add (m + 1)) ≫ d m =
      (A 0 ◁ d m) ≫ mul 0 m ≫ A.reindex (Nat.zero_add m)

/-- A derivation is determined by degree one when left multiplication by degree one generates
every higher component. -/
theorem IsDerivation.ext_left {A : GradedObject ℕ C}
    {mul : ∀ n m : ℕ, A n ⊗ A m ⟶ A (n + m)}
    {d e : A.Predifferential} [∀ n : ℕ, Epi (mul 1 (n + 1))]
    (hd : IsDerivation A mul d) (he : IsDerivation A mul e)
    (h₀ : d 0 = e 0) : d = e := sorry

/-- A derivation is determined by degree one when right multiplication by degree one generates
every higher component. -/
theorem IsDerivation.ext_right {A : GradedObject ℕ C}
    {mul : ∀ n m : ℕ, A n ⊗ A m ⟶ A (n + m)}
    {d e : A.Predifferential} [∀ n : ℕ, Epi (mul (n + 1) 1)]
    (hd : IsDerivation A mul d) (he : IsDerivation A mul e)
    (h₀ : d 0 = e 0) : d = e := sorry

end Monoidal

end CategoryTheory.GradedObject

