/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.CategoryTheory.PathCategory.MorphismProperty

/-!
# Finitely generated morphism properties

Finite generation means generation under identities and finite composition by finitely many
arrows.  For a finite-object category whose total morphism property is finitely generated, a
single finite indexing category can be chosen both initial and final.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {I : Type u} [Category.{v} I]

namespace MorphismProperty

/-- Lemma 4.18.1 (Stacks 05XU): a morphism property is finitely generated when it is the
multiplicative closure of a finite set of arrows. -/
@[stacks 05XU "finitely generated morphism properties"]
def IsFinitelyGenerated (W : MorphismProperty I) : Prop :=
  ∃ S : MorphismProperty I, S.toSet.Finite ∧ S.multiplicativeClosure = W

/-- Every finitely generated morphism property is multiplicative. -/
theorem IsFinitelyGenerated.isMultiplicative
    {W : MorphismProperty I} (h : W.IsFinitelyGenerated) :
    W.IsMultiplicative := sorry

end MorphismProperty

/-- Lemma 4.18.1 (Stacks 05XU): a finite category mapping both initially and finally to `I`, with
the same nonemptiness as `I`. -/
@[stacks 05XU "finite initial-final reduction"]
structure FiniteInitialFinalReduction (I : Type u) [Category.{v} I] where
  /-- The finite indexing category. -/
  index : Type (max u v)
  /-- The category structure on the finite index. -/
  [indexCategory : SmallCategory index]
  /-- Finiteness of the index category. -/
  [indexFinite : FinCategory index]
  /-- The comparison functor to the original category. -/
  functor : index ⥤ I
  /-- The comparison functor is initial. -/
  [initial : functor.Initial]
  /-- The comparison functor is final. -/
  [final : functor.Final]
  /-- The finite index is nonempty exactly when the original category is. -/
  nonempty_iff : Nonempty index ↔ Nonempty I

namespace FiniteInitialFinalReduction

attribute [instance] indexCategory indexFinite initial final

/-- Package a finite indexing functor that is simultaneously initial and final. -/
def ofFunctor {J : Type (max u v)} [SmallCategory J] [FinCategory J]
    (F : J ⥤ I) [F.Initial] [F.Final] (h : Nonempty J ↔ Nonempty I) :
    FiniteInitialFinalReduction I where
  index := J
  functor := F
  nonempty_iff := h

end FiniteInitialFinalReduction

namespace MorphismProperty.IsFinitelyGenerated

/-- Lemma 4.18.1 (Stacks 05XU): a finite-object category with finitely generated arrows admits a
finite reduction that is simultaneously initial and final. -/
@[stacks 05XU "finite initial-final reduction and nonemptiness comparison"]
theorem existsReduction [Finite I]
    (hgen : (⊤ : MorphismProperty I).IsFinitelyGenerated) :
    Nonempty (FiniteInitialFinalReduction I) := sorry

end MorphismProperty.IsFinitelyGenerated

end CategoryTheory
