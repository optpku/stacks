/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Uniform bounds for diagrams in a t-structure

A diagram has uniform bounds when one pair of t-structure degrees bounds every object in the
diagram. The construction is independent of any particular realization of a t-structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uC vC uI vI uJ vJ

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/-- A diagram has uniform bounds `[a, b]` for `t` when every object satisfies both
`t.IsGE _ a` and `t.IsLE _ b`. The canonical derived-category specialization is used by
Lemma 13.42.3 (0G3B). -/
@[stacks 0G3B]
def IsUniformlyBounded (t : TStructure C) {I : Type uI} [Category.{vI} I]
    (F : I ⥤ C) (a b : ℤ) : Prop :=
  ∀ i : I, t.IsGE (F.obj i) a ∧ t.IsLE (F.obj i) b

namespace IsUniformlyBounded

variable {t : TStructure C}
variable {I : Type uI} [Category.{vI} I]
variable {F G : I ⥤ C} {a b : ℤ}

/-- Every object of a uniformly bounded diagram satisfies the common lower bound. -/
theorem isGE (h : IsUniformlyBounded t F a b) (i : I) : t.IsGE (F.obj i) a := sorry

/-- Every object of a uniformly bounded diagram satisfies the common upper bound. -/
theorem isLE (h : IsUniformlyBounded t F a b) (i : I) : t.IsLE (F.obj i) b := sorry

/-- Uniform bounds are preserved by precomposing the diagram with any functor. -/
theorem whisker {J : Type uJ} [Category.{vJ} J] (h : IsUniformlyBounded t F a b)
    (G : J ⥤ I) : IsUniformlyBounded t (G ⋙ F) a b := sorry

/-- Uniform bounds transport across a natural isomorphism of diagrams. -/
theorem of_iso (h : IsUniformlyBounded t F a b) (e : F ≅ G) :
    IsUniformlyBounded t G a b := sorry

/-- A diagram bounded in `[a, b]` is bounded in every enclosing interval `[a', b']`. -/
theorem mono {a' b' : ℤ} (h : IsUniformlyBounded t F a b)
    (ha : a' ≤ a) (hb : b ≤ b') : IsUniformlyBounded t F a' b' := sorry

end IsUniformlyBounded

end CategoryTheory.Triangulated.TStructure
