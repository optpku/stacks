/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import ReasLib.CategoryTheory.Generator.Subobject
public import ReasLib.Order.Set.CardinalChain
import Mathlib.Tactic.CrossRefAttribute

/-!
# Subobject bounds from a separator

The factor-set map sends a subobject of `X` to the set of morphisms from a fixed
object that factor through it.  A separator makes this map injective, yielding chain
and cardinality bounds for subobjects.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {G X : C}

namespace Subobject

/-- The morphisms `G ⟶ X` that factor through a subobject `S` of `X`. -/
@[stacks 0E8N "factor-set owner"]
def factorSet (S : Subobject X) (G : C) : Set (G ⟶ X) :=
  { f | S.Factors f }

/-- Membership in a factor set is factorization through the corresponding subobject. -/
@[simp]
theorem mem_factorSet (G : C) (S : Subobject X) (f : G ⟶ X) :
    f ∈ S.factorSet G ↔ S.Factors f := sorry

/-- Enlarging a subobject enlarges its factor set. -/
theorem monotone_factorSet (G : C) :
    Monotone fun S : Subobject X ↦ S.factorSet G := sorry

/-- A separator distinguishes subobjects by their factor sets. -/
theorem factorSet_injective [Preadditive C] [Balanced C] [HasKernels C]
    (hG : IsSeparator G) :
    Function.Injective fun S : Subobject X ↦ S.factorSet G := sorry

namespace GeneratorBound

variable [Preadditive C] [Balanced C] [HasKernels C]

/-- Lemma 19.11.1 (1): a separator rules out an increasing subobject chain indexed by a
cardinal larger than the corresponding hom-set. -/
@[stacks 0E8N "(1), increasing chains"]
theorem noStrictMonoChain (hG : IsSeparator G) (κ : Cardinal.{v})
    (hκ : Cardinal.mk (G ⟶ X) < κ) :
    ¬ ∃ S : κ.ord.ToType → Subobject X, StrictMono S := sorry

/-- Lemma 19.11.1 (2): a separator rules out a decreasing subobject chain indexed by a
cardinal larger than the corresponding hom-set. -/
@[stacks 0E8N "(2), decreasing chains"]
theorem noStrictAntiChain (hG : IsSeparator G) (κ : Cardinal.{v})
    (hκ : Cardinal.mk (G ⟶ X) < κ) :
    ¬ ∃ S : κ.ord.ToType → Subobject X, StrictAnti S := sorry

/-- Lemma 19.11.1 (3): a monotone ordinal-indexed subobject family stabilizes when the
cofinality exceeds the cardinality of the hom-set from a separator. -/
@[stacks 0E8N "(3), increasing stabilization"]
theorem monotoneEventuallyConstant (hG : IsSeparator G) (α : Ordinal.{v})
    (hα : Cardinal.mk (G ⟶ X) < α.cof)
    (S : α.ToType → Subobject X) (hS : Monotone S) :
    ∃ i : α.ToType, ∀ j : α.ToType, i ≤ j → S j = S i := sorry

/-- Lemma 19.11.1 (4): an antitone ordinal-indexed subobject family stabilizes when the
cofinality exceeds the cardinality of the hom-set from a separator. -/
@[stacks 0E8N "(4), decreasing stabilization"]
theorem antitoneEventuallyConstant (hG : IsSeparator G) (α : Ordinal.{v})
    (hα : Cardinal.mk (G ⟶ X) < α.cof)
    (S : α.ToType → Subobject X) (hS : Antitone S) :
    ∃ i : α.ToType, ∀ j : α.ToType, i ≤ j → S j = S i := sorry

/-- Lemma 19.11.1 (5): the subobjects of `X` inject into the power set of the hom-set
from a separator. -/
@[stacks 0E8N "(5), subobject cardinality"]
theorem mk_le (hG : IsSeparator G) :
    Cardinal.mk (Subobject X) ≤ 2 ^ Cardinal.lift (Cardinal.mk (G ⟶ X)) := sorry

end GeneratorBound

end Subobject

end CategoryTheory
