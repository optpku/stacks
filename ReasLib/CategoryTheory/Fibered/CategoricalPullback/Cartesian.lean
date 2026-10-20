/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strongly cartesian arrows in categorical pullbacks

This module records the projection-level strong-cartesianness fact needed by
pushforward constructions.  It is independent of chosen cleavages, localizations, and
topologies.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits

namespace Limits.CategoricalPullback

namespace Left

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- Lemma 8.12.8 (tag 04WI): in a categorical pullback, a morphism whose second component is
strongly cartesian is strongly cartesian for the first projection. -/
@[stacks 04WI "strongly cartesian pullback projection from second component"]
theorem isStronglyCartesian_of_snd
    (u : C ⥤ D) (p : S ⥤ D) {a b : CategoricalPullback u p} (φ : a ⟶ b)
    (hφ : p.IsStronglyCartesian (p.map φ.snd) φ.snd) :
    (π₁ u p).IsStronglyCartesian ((π₁ u p).map φ) φ := sorry

/-- Lemma 8.12.8 (tag 04WI): if `p` is fibered, a strongly cartesian morphism for the left
projection of a categorical pullback has strongly cartesian second component. -/
@[stacks 04WI "strongly cartesian second component from pullback projection"]
theorem snd_isStronglyCartesian_of_left
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {a b : CategoricalPullback u p} (φ : a ⟶ b)
    (hφ : (π₁ u p).IsStronglyCartesian ((π₁ u p).map φ) φ) :
    p.IsStronglyCartesian (p.map φ.snd) φ.snd := sorry

/-- Lemma 8.12.8 (tag 04WI): for a categorical pullback over a fibered functor, strong
cartesianness for the left projection is equivalent to strong cartesianness of the second
component. -/
@[stacks 04WI "strongly cartesian pullback projection criterion"]
theorem isStronglyCartesian_iff_snd
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {a b : CategoricalPullback u p} (φ : a ⟶ b) :
    (π₁ u p).IsStronglyCartesian ((π₁ u p).map φ) φ ↔
      p.IsStronglyCartesian (p.map φ.snd) φ.snd := sorry

end Left

end Limits.CategoricalPullback

end CategoryTheory
