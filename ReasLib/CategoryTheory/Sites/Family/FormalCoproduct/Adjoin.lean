/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Objects
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adding entries to fixed-target formal coproducts

This leaf owns the concrete operation of adjoining one arrow to a fixed-target formal
coproduct family and its source-membership computation rule.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- Adjoin one arrow `U' ⟶ X` to a fixed-target formal coproduct family over `X`. -/
@[stacks 0DAV "single-arrow extension"]
abbrev addSingleton {X U' : C}
    (𝒰 : FormalCoproduct (Over X)) (f : U' ⟶ X) : FormalCoproduct (Over X) :=
  ofArrows
    (fun s : Sum 𝒰.index Unit ↦
      match s with
      | .inl i => (𝒰.obj i).left
      | .inr _ => U')
    (fun s : Sum 𝒰.index Unit ↦
      match s with
      | .inl i => (𝒰.obj i).hom
      | .inr _ => f)

/-- Unfolding `addSingleton` gives the disjoint union of the original family and the supplied
single arrow. -/
@[simp] theorem addSingleton_def {X U' : C}
    (𝒰 : FormalCoproduct (Over X)) (f : U' ⟶ X) :
    𝒰.addSingleton f =
      ofArrows
        (fun s : Sum 𝒰.index Unit ↦
          match s with
          | .inl i => (𝒰.obj i).left
          | .inr _ => U')
        (fun s : Sum 𝒰.index Unit ↦
          match s with
          | .inl i => (𝒰.obj i).hom
          | .inr _ => f) := sorry

/-- The sources of an adjoined family lie in `B` exactly when the original sources do and the
adjoined source lies in `B`. -/
@[simp, stacks 0DAV "single-arrow source membership"]
theorem addSingleton_objectsIn_iff
    {X U' : C} (𝒰 : FormalCoproduct (Over X)) (f : U' ⟶ X) (B : Set C) :
    Over.objectsIn (𝒰.addSingleton f) B ↔
      Over.objectsIn 𝒰 B ∧ U' ∈ B := sorry

end CategoryTheory.Limits.FormalCoproduct
