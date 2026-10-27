/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Limits.Colimit.Representable

/-!
# Ordinal-indexed small objects relative to a morphism property

This file separates the two pieces of an ordinal-smallness assertion: an ordinal-indexed
diagram whose arrows lie in a morphism property, and preservation of its colimit by a
corepresentable functor. It does not impose continuity at limit stages or any of the additional
cardinality hypotheses used by the small object argument.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- An `α`-indexed diagram in which every structure morphism belongs to `I`.

This is deliberately weaker than a transfinite composition: it records no continuity condition
at limit stages. Structure morphisms include identities; for a property which need not contain
identities, use `IsStrictOrdinalDiagram`. -/
@[stacks 05NS "ordinal diagram relative to a morphism property"]
def IsOrdinalDiagram (I : MorphismProperty C) {α : Ordinal.{w}} (B : α.ToType ⥤ C) : Prop :=
  ∀ ⦃j j' : α.ToType⦄ (f : j ⟶ j'), I (B.map f)

/-- An `α`-indexed diagram whose strict transitions belong to `I`, without requiring identities
to belong to `I`. -/
@[stacks 05NS "strict ordinal diagram relative to a morphism property"]
def IsStrictOrdinalDiagram (I : MorphismProperty C) {α : Ordinal.{w}}
    (B : α.ToType ⥤ C) : Prop :=
  ∀ ⦃j j' : α.ToType⦄ (h : j < j'), I (B.map (homOfLE h.le))

/-- Every structure morphism of an ordinal diagram belongs to its morphism property. -/
@[stacks 05NS "ordinal diagram transition"]
theorem IsOrdinalDiagram.map_mem
    {I : MorphismProperty C} {α : Ordinal.{w}} {B : α.ToType ⥤ C}
    (hB : I.IsOrdinalDiagram B) {j j' : α.ToType} (f : j ⟶ j') :
    I (B.map f) := hB f

/-- Enlarging a morphism property preserves the property of being an ordinal diagram. -/
@[stacks 05NS "enlarging the transition property"]
theorem IsOrdinalDiagram.ofLE
    {I J : MorphismProperty C} {α : Ordinal.{w}} {B : α.ToType ⥤ C}
    (hB : I.IsOrdinalDiagram B) (hIJ : I ≤ J) : J.IsOrdinalDiagram B := by
  intro j j' f
  exact hIJ _ (hB f)

/-- Every strict transition of a strict ordinal diagram belongs to its morphism property. -/
@[stacks 05NS "strict ordinal diagram transition"]
theorem IsStrictOrdinalDiagram.map_mem
    {I : MorphismProperty C} {α : Ordinal.{w}} {B : α.ToType ⥤ C}
    (hB : I.IsStrictOrdinalDiagram B) {j j' : α.ToType} (h : j < j') :
    I (B.map (homOfLE h.le)) := hB h

/-- Enlarging a morphism property preserves the property of being a strict ordinal diagram. -/
@[stacks 05NS "enlarging the strict transition property"]
theorem IsStrictOrdinalDiagram.ofLE
    {I J : MorphismProperty C} {α : Ordinal.{w}} {B : α.ToType ⥤ C}
    (hB : I.IsStrictOrdinalDiagram B) (hIJ : I ≤ J) :
    J.IsStrictOrdinalDiagram B := by
  intro j j' h
  exact hIJ _ (hB h)

/-- Forgetting identity transitions sends an ordinal diagram to a strict ordinal diagram. -/
@[stacks 05NS "forgetting identity transitions"]
theorem IsOrdinalDiagram.toStrict
    {I : MorphismProperty C} {α : Ordinal.{w}} {B : α.ToType ⥤ C}
    (hB : I.IsOrdinalDiagram B) : I.IsStrictOrdinalDiagram B := by
  intro j j' h
  exact hB (homOfLE h.le)

/-- If `I` contains identities, a strict ordinal diagram is an ordinal diagram. -/
@[stacks 05NS "adjoining identity transitions"]
theorem IsStrictOrdinalDiagram.toOrdinal
    {I : MorphismProperty C} [I.ContainsIdentities]
    {α : Ordinal.{w}} {B : α.ToType ⥤ C} (hB : I.IsStrictOrdinalDiagram B) :
    I.IsOrdinalDiagram B := by
  intro j j' f
  rcases eq_or_lt_of_le (leOfHom f) with h | h
  · subst j'
    have hf : f = 𝟙 j := Subsingleton.elim _ _
    rw [hf, B.map_id]
    exact I.id_mem (B.obj j)
  · have hf : f = homOfLE h.le := Subsingleton.elim _ _
    rw [hf]
    exact hB h

/-- For a morphism property containing identities, the ordinary and strict notions of ordinal
diagram agree. -/
@[stacks 05NS "ordinary and strict ordinal diagrams"]
theorem isOrdinalDiagram_iff_isStrictOrdinalDiagram
    {I : MorphismProperty C} [I.ContainsIdentities]
    {α : Ordinal.{w}} {B : α.ToType ⥤ C} :
    I.IsOrdinalDiagram B ↔ I.IsStrictOrdinalDiagram B :=
  ⟨IsOrdinalDiagram.toStrict, IsStrictOrdinalDiagram.toOrdinal⟩

/-- An object `A` is `α`-small relative to `I` when `Hom(A, -)` preserves the colimit of every
`α`-indexed diagram whose structure morphisms belong to `I`.

For any fixed diagram, `PreservesColimit B (coyoneda.obj (op A))` remains the canonical
comparison-map API. -/
@[stacks 05NS]
def IsOrdinalSmall (I : MorphismProperty C) (A : C) (α : Ordinal.{w}) : Prop :=
  ∀ (B : α.ToType ⥤ C) (_ : I.IsOrdinalDiagram B),
    PreservesColimit B (coyoneda.obj (Opposite.op A))

/-- An object is strictly `α`-small relative to `I` when its corepresentable functor preserves
the colimit of every `α`-indexed diagram whose nonidentity transitions belong to `I`.

Unlike `IsOrdinalSmall`, this predicate remains meaningful when `I` does not contain identity
morphisms. -/
@[stacks 05NS "strict ordinal smallness"]
def IsStrictOrdinalSmall (I : MorphismProperty C) (A : C) (α : Ordinal.{w}) : Prop :=
  ∀ (B : α.ToType ⥤ C) (_ : I.IsStrictOrdinalDiagram B),
    PreservesColimit B (coyoneda.obj (Opposite.op A))

/-- Strict ordinal smallness implies ordinal smallness by forgetting identity transitions. -/
@[stacks 05NS "strict-to-ordinary smallness"]
theorem IsStrictOrdinalSmall.toOrdinal
    {I : MorphismProperty C} {A : C} {α : Ordinal.{w}}
    (hA : I.IsStrictOrdinalSmall A α) : I.IsOrdinalSmall A α := by
  intro B hB
  exact hA B hB.toStrict

/-- If `I` contains identities, ordinal smallness also controls diagrams specified only by their
strict transitions. -/
@[stacks 05NS "ordinary-to-strict smallness"]
theorem IsOrdinalSmall.toStrict
    {I : MorphismProperty C} [I.ContainsIdentities] {A : C} {α : Ordinal.{w}}
    (hA : I.IsOrdinalSmall A α) : I.IsStrictOrdinalSmall A α := by
  intro B hB
  exact hA B hB.toOrdinal

/-- For a morphism property containing identities, ordinary and strict ordinal smallness agree. -/
@[stacks 05NS "ordinary and strict ordinal smallness"]
theorem isOrdinalSmall_iff_isStrictOrdinalSmall
    {I : MorphismProperty C} [I.ContainsIdentities] {A : C} {α : Ordinal.{w}} :
    I.IsOrdinalSmall A α ↔ I.IsStrictOrdinalSmall A α :=
  ⟨IsOrdinalSmall.toStrict, IsStrictOrdinalSmall.toOrdinal⟩

/-- Ordinal smallness is contravariant in the morphism property: an object small relative to
`J` is small relative to every subproperty `I ≤ J`. -/
@[stacks 05NS "restricting the transition property"]
theorem IsOrdinalSmall.ofLE
    {I J : MorphismProperty C} {A : C} {α : Ordinal.{w}}
    (hA : J.IsOrdinalSmall A α) (hIJ : I ≤ J) : I.IsOrdinalSmall A α := by
  intro B hB
  exact hA B (hB.ofLE hIJ)

/-- Strict ordinal smallness is contravariant in the morphism property. -/
@[stacks 05NS "restricting the strict transition property"]
theorem IsStrictOrdinalSmall.ofLE
    {I J : MorphismProperty C} {A : C} {α : Ordinal.{w}}
    (hA : J.IsStrictOrdinalSmall A α) (hIJ : I ≤ J) :
    I.IsStrictOrdinalSmall A α := by
  intro B hB
  exact hA B (hB.ofLE hIJ)

/-- The corepresentable functor preserves any ordinal colimit covered by an ordinal-smallness
hypothesis. This cone-level API does not require chosen colimit instances. -/
@[stacks 05NS "ordinal colimit preservation"]
theorem IsOrdinalSmall.preservesColimit
    {I : MorphismProperty C} {A : C} {α : Ordinal.{w}}
    (hA : I.IsOrdinalSmall A α) (B : α.ToType ⥤ C)
    (hB : I.IsOrdinalDiagram B) :
    PreservesColimit B (coyoneda.obj (Opposite.op A)) := hA B hB

/-- The corepresentable functor preserves any strict ordinal colimit covered by a strict
ordinal-smallness hypothesis. -/
@[stacks 05NS "strict ordinal colimit preservation"]
theorem IsStrictOrdinalSmall.preservesColimit
    {I : MorphismProperty C} {A : C} {α : Ordinal.{w}}
    (hA : I.IsStrictOrdinalSmall A α) (B : α.ToType ⥤ C)
    (hB : I.IsStrictOrdinalDiagram B) :
    PreservesColimit B (coyoneda.obj (Opposite.op A)) := hA B hB

/-- The canonical Hom-colimit comparison is bijective for every ordinal diagram covered by an
ordinal-smallness hypothesis. -/
@[stacks 05NS "Hom-colimit comparison"]
theorem IsOrdinalSmall.colimitPost_bijective
    {I : MorphismProperty C} {A : C} {α : Ordinal.{w}}
    (hA : I.IsOrdinalSmall A α) (B : α.ToType ⥤ C)
    (hB : I.IsOrdinalDiagram B) [HasColimit B]
    [HasColimit (B ⋙ coyoneda.obj (Opposite.op A))] :
    Function.Bijective (colimit.post B (coyoneda.obj (Opposite.op A))) := by
  letI := hA B hB
  exact (isIso_iff_bijective _).mp inferInstance

/-- The canonical Hom-colimit comparison is bijective for every strict ordinal diagram covered
by a strict ordinal-smallness hypothesis. -/
@[stacks 05NS "strict Hom-colimit comparison"]
theorem IsStrictOrdinalSmall.colimitPost_bijective
    {I : MorphismProperty C} {A : C} {α : Ordinal.{w}}
    (hA : I.IsStrictOrdinalSmall A α) (B : α.ToType ⥤ C)
    (hB : I.IsStrictOrdinalDiagram B) [HasColimit B]
    [HasColimit (B ⋙ coyoneda.obj (Opposite.op A))] :
    Function.Bijective (colimit.post B (coyoneda.obj (Opposite.op A))) := by
  letI := hA B hB
  exact (isIso_iff_bijective _).mp inferInstance

end MorphismProperty

end CategoryTheory
