/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.CategoryTheory.Preadditive.LeftExact

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRing

/-- A commutative ring whose positive right-derived functors vanish for every
left exact functor from modules to abelian groups is a finite product of fields. -/
theorem exists_pi_field_of_leftExact_rightDerived_eq_zero
    {R : Type u} [CommRing R]
    (h : ∀ (F : ModuleCat.{u} R ⥤ AddCommGrpCat.{u}) [PreservesFiniteLimits F],
      ∀ n : ℕ, 0 < n → ∀ M : ModuleCat.{u} R,
        IsZero ((F.rightDerived n).obj M)) :
    ∃ (n : ℕ) (K : Fin n → Type u) (_ : ∀ i, Field (K i)),
      Nonempty (R ≃+* ((i : Fin n) → K i)) := sorry

end CommRing
