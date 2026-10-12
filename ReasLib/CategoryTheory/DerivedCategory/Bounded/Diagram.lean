/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.Triangulated.TStructure.UniformlyBounded
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Uniform bounds for diagrams in a derived category

This module specializes the uniform-bound API for t-structures to the canonical t-structure on a
derived category. The bounds remain explicit data because different applications naturally use
different intervals.
-/

@[expose] public section

open CategoryTheory

universe w u v uI vI uJ vJ

namespace CategoryTheory.DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- A diagram in a derived category has uniform cohomological bounds `[a, b]` when every one of
its objects satisfies both `IsGE a` and `IsLE b`. This is the canonical-t-structure specialization
of `Triangulated.TStructure.IsUniformlyBounded` used by Lemma 13.42.3 (0G3B). -/
@[stacks 0G3B]
abbrev IsUniformlyBounded {I : Type uI} [Category.{vI} I]
    (F : I ⥤ DerivedCategory A) (a b : ℤ) : Prop :=
  Triangulated.TStructure.IsUniformlyBounded DerivedCategory.TStructure.t F a b

namespace IsUniformlyBounded

variable {I : Type uI} [Category.{vI} I]
variable {F G : I ⥤ DerivedCategory A} {a b : ℤ}

/-- Every object of a uniformly bounded derived diagram satisfies the common lower bound. -/
theorem isGE (h : IsUniformlyBounded F a b) (i : I) : (F.obj i).IsGE a := sorry

/-- Every object of a uniformly bounded derived diagram satisfies the common upper bound. -/
theorem isLE (h : IsUniformlyBounded F a b) (i : I) : (F.obj i).IsLE b := sorry

/-- Uniform bounds are preserved by precomposing the diagram with any functor. -/
theorem whisker {J : Type uJ} [Category.{vJ} J] (h : IsUniformlyBounded F a b)
    (G : J ⥤ I) : IsUniformlyBounded (G ⋙ F) a b := sorry

/-- Uniform bounds transport across a natural isomorphism of diagrams. -/
theorem of_iso (h : IsUniformlyBounded F a b) (e : F ≅ G) :
    IsUniformlyBounded G a b := sorry

/-- A diagram bounded in `[a, b]` is bounded in every enclosing interval `[a', b']`. -/
theorem mono {a' b' : ℤ} (h : IsUniformlyBounded F a b)
    (ha : a' ≤ a) (hb : b ≤ b') : IsUniformlyBounded F a' b' := sorry

end IsUniformlyBounded

end CategoryTheory.DerivedCategory
