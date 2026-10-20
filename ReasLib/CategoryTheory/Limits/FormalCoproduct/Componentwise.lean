/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Component maps in diagrams of formal coproducts

This leaf exposes the index and object morphisms induced by an arrow in a contravariant diagram
of formal coproducts. It also packages the reusable condition that such morphisms are
componentwise isomorphisms.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory.Limits.FormalCoproduct

open Opposite

variable {C : Type u} [Category.{v} C]
variable {I : Type u'} [Category.{v'} I]

namespace Componentwise

/-- A morphism of formal coproducts is componentwise an isomorphism when each of its object
morphisms is an isomorphism. -/
@[stacks 0DAU "componentwise isomorphism of formal coproducts"]
def IsIso {K L : FormalCoproduct.{w} C} (f : K ⟶ L) : Prop :=
  ∀ a : K.I, CategoryTheory.IsIso (f.φ a)

/-- Characterization of componentwise-isomorphism morphisms of formal coproducts. -/
@[simp]
theorem isIso_iff {K L : FormalCoproduct.{w} C} (f : K ⟶ L) :
    IsIso f ↔ ∀ a : K.I, CategoryTheory.IsIso (f.φ a) := sorry

/-- Every object morphism of a componentwise-isomorphism morphism is an isomorphism. -/
theorem IsIso.component {K L : FormalCoproduct.{w} C} {f : K ⟶ L}
    (hf : IsIso f) (a : K.I) : CategoryTheory.IsIso (f.φ a) := sorry

end Componentwise

/-- The target index selected by an arrow in a contravariant diagram of formal coproducts. -/
@[stacks 0DAU "component index of a formal-coproduct diagram"]
abbrev componentIndex (K : Iᵒᵖ ⥤ FormalCoproduct.{w} C) {i j : I} (φ : i ⟶ j)
    (a : (K.obj (op j)).I) : (K.obj (op i)).I :=
  (K.map φ.op).f a

/-- The component index is computed by the reindexing function of the diagram map. -/
@[simp]
theorem componentIndex_apply (K : Iᵒᵖ ⥤ FormalCoproduct.{w} C)
    {i j : I} (φ : i ⟶ j) (a : (K.obj (op j)).I) :
    componentIndex K φ a = (K.map φ.op).f a := sorry

/-- The object morphism selected by an arrow and an index in a contravariant diagram of formal
coproducts. -/
@[stacks 0DAU "component map of a formal-coproduct diagram"]
abbrev componentMap (K : Iᵒᵖ ⥤ FormalCoproduct.{w} C) {i j : I} (φ : i ⟶ j)
    (a : (K.obj (op j)).I) :
    (K.obj (op j)).obj a ⟶ (K.obj (op i)).obj (componentIndex K φ a) :=
  (K.map φ.op).φ a

/-- The component map is computed by the corresponding object morphism of the diagram map. -/
@[simp]
theorem componentMap_apply (K : Iᵒᵖ ⥤ FormalCoproduct.{w} C)
    {i j : I} (φ : i ⟶ j) (a : (K.obj (op j)).I) :
    componentMap K φ a = (K.map φ.op).φ a := sorry

namespace Componentwise

/-- Every epimorphism in the indexing category induces a componentwise isomorphism in the
contravariant formal-coproduct diagram. -/
@[stacks 0DAU "componentwise isomorphisms on epimorphisms"]
def IsoOnEpis (K : Iᵒᵖ ⥤ FormalCoproduct.{w} C) : Prop :=
  ∀ {i j : I} (φ : i ⟶ j) [Epi φ], IsIso (K.map φ.op)

/-- The epi criterion is equivalently the pointwise isomorphism condition on every component
map induced by an epimorphism. -/
theorem isoOnEpis_iff (K : Iᵒᵖ ⥤ FormalCoproduct.{w} C) :
    IsoOnEpis K ↔
      ∀ {i j : I} (φ : i ⟶ j) [Epi φ] (a : (K.obj (op j)).I),
        CategoryTheory.IsIso (componentMap K φ a) := sorry

/-- An epimorphism induces a componentwise-isomorphism morphism under the epi criterion. -/
theorem IsoOnEpis.map {K : Iᵒᵖ ⥤ FormalCoproduct.{w} C}
    (hK : IsoOnEpis K) {i j : I} (φ : i ⟶ j) [Epi φ] :
    IsIso (K.map φ.op) := sorry

/-- Under the epi criterion, every component map induced by an epimorphism is an isomorphism. -/
theorem IsoOnEpis.component {K : Iᵒᵖ ⥤ FormalCoproduct.{w} C}
    (hK : IsoOnEpis K) {i j : I} (φ : i ⟶ j) [Epi φ]
    (a : (K.obj (op j)).I) : CategoryTheory.IsIso (componentMap K φ a) := sorry

end Componentwise

end CategoryTheory.Limits.FormalCoproduct
