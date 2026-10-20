/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup.Additivity
public import ReasLib.CategoryTheory.Pretriangulated.Homological.ShiftVanishing
public import ReasLib.CategoryTheory.Pretriangulated.K0.GrothendieckGroup
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Interval
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Euler Maps on Triangulated Grothendieck Groups

For a shifted homological functor with finite shift support, this leaf builds
the alternating Euler class of an object and its induced homomorphism on
triangulated `K₀`.  The construction is independent of derived categories;
bounded-derived and weak-Serre applications should import this leaf directly.

## Main declarations

* `Functor.eulerClass` is the objectwise alternating `K₀` class.
* `Functor.eulerClass_eq_sum_of_vanishingIn` is its finite computation rule.
* `Functor.eulerK0Map` is the induced map on `TriangulatedK0`.
-/

open CategoryTheory Limits Pretriangulated ZeroObject
open scoped BigOperators

universe vD vA uD uA

namespace CategoryTheory.Functor

section EulerClass

variable {D : Type uD} [Category.{vD} D] [HasShift D ℤ]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (H : D ⥤ A) [H.ShiftSequence ℤ]

/-- The alternating Euler class of `X`, written as a finitely supported sum of shifted values of
`H`. -/
@[stacks 0FCR]
noncomputable def eulerClass (X : D) : AbelianK0 A :=
  ∑ᶠ i : ℤ, i.negOnePow • K₀[(H.shift i).obj X]

/-- Bounded shift vanishing gives finite support for the summands defining `eulerClass`. -/
@[stacks 0FCR]
theorem eulerClass_hasFiniteSupport (X : D) (hX : H.shiftVanishingBounded X) :
    Function.HasFiniteSupport
      (fun i : ℤ ↦ i.negOnePow • K₀[(H.shift i).obj X]) := sorry

/-- If the shifted values of `H` on `X` vanish outside `[a, b]`, its Euler class is the
corresponding finite interval sum. -/
@[stacks 0FCR]
theorem eulerClass_eq_sum_of_vanishingIn (X : D) {a b : ℤ}
    (hX : H.shiftVanishingIn a b X) :
    H.eulerClass X =
      Finset.sum (Finset.Icc a b) (fun i ↦ i.negOnePow • K₀[(H.shift i).obj X]) := sorry

/-- Isomorphic objects have the same Euler class. -/
theorem eulerClass_eq_of_iso {X Y : D} (e : X ≅ Y) :
    H.eulerClass X = H.eulerClass Y := sorry

/-- Naturally isomorphic shifted functors have the same Euler class on every
object. -/
theorem eulerClass_eq_of_natIso {G : D ⥤ A} [G.ShiftSequence ℤ]
    (e : H ≅ G) (X : D) :
    H.eulerClass X = G.eulerClass X := sorry

end EulerClass

section EulerK0Map

variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (H : D ⥤ A) [H.IsHomological] [H.ShiftSequence ℤ]

/-- The Euler class is additive on a distinguished triangle whenever its
three vertices have bounded shift support. -/
theorem eulerClass_distinguished (T : Triangle D) (hT : T ∈ distTriang D)
    (h₁ : H.shiftVanishingBounded T.obj₁)
    (h₂ : H.shiftVanishingBounded T.obj₂)
    (h₃ : H.shiftVanishingBounded T.obj₃) :
    H.eulerClass T.obj₂ = H.eulerClass T.obj₁ + H.eulerClass T.obj₃ := sorry

/-- The alternating Euler class kills the relations of distinguished triangles when every object
has bounded shift support. -/
@[stacks 0FCR]
theorem relations_le_ker_eulerClass
    (hH : ∀ X : D, H.shiftVanishingBounded X) :
    TriangulatedK0.relations D ≤
      (FreeAbelianGroup.lift fun X ↦ H.eulerClass X).ker := sorry

/-- The homomorphism on triangulated `K₀` induced by a shifted homological functor with bounded
shift support. -/
@[stacks 0FCR]
noncomputable def eulerK0Map (hH : ∀ X : D, H.shiftVanishingBounded X) :
    TriangulatedK0 D →+ AbelianK0 A :=
  TriangulatedK0.lift (fun X ↦ H.eulerClass X) (H.relations_le_ker_eulerClass hH)

/-- The Euler map evaluates on an object class as its alternating Euler class. -/
@[stacks 0FCR, simp]
theorem eulerK0Map_apply_of
    (hH : ∀ X : D, H.shiftVanishingBounded X) (X : D) :
    H.eulerK0Map hH (TriangulatedK0.of X) = H.eulerClass X := sorry

end EulerK0Map

end CategoryTheory.Functor
