/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.AddCommGrp
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.CountableLimit
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.ShortExact

/-!
# Limits of sequential Mittag-Leffler systems

The statements here separate formal left exactness of limits from the additional
Mittag-Leffler hypothesis that supplies right exactness for sequential abelian-group systems.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

namespace ShortComplex.ShortExact

variable {A : Type u} [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]

/-- Lemma 12.31.3 [02N1] (1): a sequential limit sends a short exact row in an abelian category
to an exact row. No Mittag-Leffler hypothesis is needed for this left-exact component. -/
@[stacks 02N1]
theorem limit_exact {S : ShortComplex (SequentialInverseSystem A)}
    (hS : S.ShortExact) :
    (S.map (lim : SequentialInverseSystem A ⥤ A)).Exact := sorry

/-- Lemma 12.31.3 [02N1] (1): the left map of the limit row of a short exact sequence of
sequential inverse systems is monic. -/
@[stacks 02N1]
theorem limit_mono_f {S : ShortComplex (SequentialInverseSystem A)}
    (hS : S.ShortExact) :
    Mono (S.map (lim : SequentialInverseSystem A ⥤ A)).f := sorry

end ShortComplex.ShortExact

namespace ModuleCat.ShortExact

variable {R : Type v} [Ring R]

/-- A short exact row of sequential module systems remains short exact after taking limits when
its left term is Mittag-Leffler. -/
@[stacks 02N1 "module-valued Mittag-Leffler limit"]
theorem limit_of_isMittagLeffler
    {S : ShortComplex (SequentialInverseSystem (ModuleCat.{v} R))}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) :
    (S.map (lim : SequentialInverseSystem (ModuleCat.{v} R) ⥤ ModuleCat.{v} R)).ShortExact :=
  sorry

end ModuleCat.ShortExact

namespace ShortComplex.ShortExact

/-- Lemma 12.31.3 [02N1] (3): a short exact row of sequential abelian-group systems remains
short exact after taking limits when its left term is Mittag-Leffler. -/
@[stacks 02N1]
theorem limit_of_isMittagLeffler
    {S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})} (hS : S.ShortExact)
    (hX₁ : S.X₁.IsMittagLeffler) :
    (S.map (lim : SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v})).ShortExact := sorry

end ShortComplex.ShortExact

namespace ComposableArrows.Exact

/-- Lemma 12.31.4 [070B]: for an exact four-term row of sequential abelian-group systems, the
tail remains exact after taking limits when the leftmost term is Mittag-Leffler. -/
@[stacks 070B]
theorem limit_tail_of_isMittagLeffler
    {S : ComposableArrows (SequentialInverseSystem AddCommGrpCat.{v}) 3} (hS : S.Exact)
    (hleft : S.left.IsMittagLeffler) :
    (ComposableArrows.δ₀
      (S ⋙ (lim : SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v}))).Exact := sorry

end ComposableArrows.Exact

end CategoryTheory
