/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Iso
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Category

/-!
# Free graded algebras with divided powers

This file builds on the category of graded divided-power algebras and isolates the universal
property of a free presentation by a graded set of generators. It also supplies the canonical
comparison and isomorphism between any two realizations of the same free presentation.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DirectSum

universe u v w

namespace DividedPowerGradedAlgebra

variable {R : Type u} [CommRing R]

/-- A graded divided-power polynomial presentation, characterized by the universal property of
the free strictly graded-commutative divided-power algebra on a graded set of generators. -/
@[stacks 09PN "free graded divided-power algebra presentation"]
structure FreePresentation
    (A : DividedPowerGradedAlgebra.{u, v} R) (generators : ℕ → Type w) where
  /-- The homogeneous generator in its declared degree. -/
  generator (n : ℕ) : generators n → A.toGradedAlgebra.piece n
  /-- Every degree-preserving assignment of generators extends to a divided-power homomorphism. -/
  lift {B : DividedPowerGradedAlgebra.{u, v} R}
    (x : ∀ n : ℕ, generators n → B.toGradedAlgebra.piece n) : A ⟶ B
  /-- The lifted homomorphism has the prescribed values on generators. -/
  lift_generator {B : DividedPowerGradedAlgebra.{u, v} R}
    (x : ∀ n : ℕ, generators n → B.toGradedAlgebra.piece n)
    (n : ℕ) (i : generators n) :
    (lift x).toGradedHom.map n (generator n i) = x n i
  /-- A divided-power homomorphism out of the presentation is determined by the generators. -/
  hom_ext {B : DividedPowerGradedAlgebra.{u, v} R} (f g : A ⟶ B)
    (h : ∀ n : ℕ, ∀ i : generators n,
      f.toGradedHom.map n (generator n i) =
        g.toGradedHom.map n (generator n i)) :
    f = g

attribute [simp] FreePresentation.lift_generator

namespace FreePresentation

variable {A : DividedPowerGradedAlgebra.{u, v} R} {generators : ℕ → Type w}

/-- A divided-power graded-algebra homomorphism is the canonical lift exactly when it has the
prescribed values on the free generators. -/
@[simp] theorem lift_unique (P : FreePresentation A generators)
    {B : DividedPowerGradedAlgebra.{u, v} R}
    (x : ∀ n : ℕ, generators n → B.toGradedAlgebra.piece n) (f : A ⟶ B) :
    (∀ n : ℕ, ∀ i : generators n,
      f.toGradedHom.map n (P.generator n i) = x n i) ↔ f = P.lift x := sorry

/-- A degree-preserving assignment of the generators has a unique extension to a
divided-power graded-algebra homomorphism. -/
theorem existsUnique_lift (P : FreePresentation A generators)
    {B : DividedPowerGradedAlgebra.{u, v} R}
    (x : ∀ n : ℕ, generators n → B.toGradedAlgebra.piece n) :
    ∃! f : A ⟶ B, ∀ n : ℕ, ∀ i : generators n,
      f.toGradedHom.map n (P.generator n i) = x n i := sorry

/-- Every morphism out of a free presentation is the lift of its values on the generators. -/
theorem hom_eq_lift (P : FreePresentation A generators)
    {B : DividedPowerGradedAlgebra.{u, v} R} (f : A ⟶ B) :
    f = P.lift (fun n i ↦ f.toGradedHom.map n (P.generator n i)) := sorry

/-- Lifting the generator family of a free presentation gives the identity morphism. -/
@[simp]
theorem lift_generators (P : FreePresentation A generators) :
    P.lift P.generator = 𝟙 A := sorry

/-- Postcomposing a free lift is the lift of the postcomposed generator assignment. -/
@[simp]
theorem lift_comp (P : FreePresentation A generators)
    {B C : DividedPowerGradedAlgebra.{u, v} R}
    (x : ∀ n : ℕ, generators n → B.toGradedAlgebra.piece n) (f : B ⟶ C) :
    P.lift x ≫ f =
      P.lift (fun n i ↦ f.toGradedHom.map n (x n i)) := sorry

variable {B C : DividedPowerGradedAlgebra.{u, v} R}

/-- The canonical comparison from one realization of a free graded divided-power presentation to
another sends each source generator to the corresponding target generator. -/
def comparison (P : FreePresentation A generators) (Q : FreePresentation B generators) :
    A ⟶ B :=
  P.lift Q.generator

/-- The canonical comparison sends every source generator to the corresponding target
generator. -/
@[simp]
theorem comparison_generator (P : FreePresentation A generators)
    (Q : FreePresentation B generators) (n : ℕ) (i : generators n) :
    (P.comparison Q).toGradedHom.map n (P.generator n i) = Q.generator n i := sorry

/-- A morphism between two free presentations that sends corresponding generators to one another
is the canonical comparison. -/
theorem comparison_unique (P : FreePresentation A generators)
    (Q : FreePresentation B generators) (f : A ⟶ B)
    (hf : ∀ n : ℕ, ∀ i : generators n,
      f.toGradedHom.map n (P.generator n i) = Q.generator n i) :
    f = P.comparison Q := sorry

/-- There is a unique morphism between two free presentations that sends corresponding generators
to one another. -/
theorem existsUnique_comparison (P : FreePresentation A generators)
    (Q : FreePresentation B generators) :
    ∃! f : A ⟶ B, ∀ n : ℕ, ∀ i : generators n,
      f.toGradedHom.map n (P.generator n i) = Q.generator n i := sorry

/-- The canonical comparison from a free presentation to itself is the identity. -/
@[simp]
theorem comparison_self (P : FreePresentation A generators) :
    P.comparison P = 𝟙 A := sorry

/-- Canonical comparisons of free presentations compose transitively. -/
@[simp]
theorem comparison_comp (P : FreePresentation A generators)
    (Q : FreePresentation B generators) (S : FreePresentation C generators) :
    P.comparison Q ≫ Q.comparison S = P.comparison S := sorry

/-- The forward and backward comparisons between two free presentations compose to the identity
on the source presentation. -/
theorem comparison_hom_inv_id (P : FreePresentation A generators)
    (Q : FreePresentation B generators) :
    P.comparison Q ≫ Q.comparison P = 𝟙 A := sorry

/-- The backward and forward comparisons between two free presentations compose to the identity
on the target presentation. -/
theorem comparison_inv_hom_id (P : FreePresentation A generators)
    (Q : FreePresentation B generators) :
    Q.comparison P ≫ P.comparison Q = 𝟙 B := sorry

/-- The canonical isomorphism between two realizations of the same free graded divided-power
presentation. -/
@[stacks 09PN "canonical free-presentation comparison"]
def comparisonIso (P : FreePresentation A generators)
    (Q : FreePresentation B generators) : A ≅ B where
  hom := P.comparison Q
  inv := Q.comparison P
  hom_inv_id := P.comparison_hom_inv_id Q
  inv_hom_id := P.comparison_inv_hom_id Q

/-- The forward map of the canonical free-presentation isomorphism is the canonical comparison. -/
@[simp]
theorem comparisonIso_hom (P : FreePresentation A generators)
    (Q : FreePresentation B generators) :
    (P.comparisonIso Q).hom = P.comparison Q := sorry

/-- The inverse map of the canonical free-presentation isomorphism is the reverse comparison. -/
@[simp]
theorem comparisonIso_inv (P : FreePresentation A generators)
    (Q : FreePresentation B generators) :
    (P.comparisonIso Q).inv = Q.comparison P := sorry

/-- The canonical isomorphism from a free presentation to itself is the identity isomorphism. -/
@[simp]
theorem comparisonIso_self (P : FreePresentation A generators) :
    P.comparisonIso P = Iso.refl A := sorry

/-- Reversing a canonical free-presentation isomorphism exchanges its two presentations. -/
@[simp]
theorem comparisonIso_symm (P : FreePresentation A generators)
    (Q : FreePresentation B generators) :
    (P.comparisonIso Q).symm = Q.comparisonIso P := sorry

/-- Canonical free-presentation isomorphisms compose transitively. -/
@[simp]
theorem comparisonIso_trans (P : FreePresentation A generators)
    (Q : FreePresentation B generators) (S : FreePresentation C generators) :
    (P.comparisonIso Q).trans (Q.comparisonIso S) = P.comparisonIso S := sorry

end FreePresentation

end DividedPowerGradedAlgebra
