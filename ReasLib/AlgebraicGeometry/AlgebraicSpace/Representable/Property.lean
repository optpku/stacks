/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Pullback
public import ReasLib.CategoryTheory.MorphismProperty.RepresentedTests

/-!
# Relative morphism properties for maps representable by algebraic spaces

A morphism property of algebraic spaces over `S` transfers to morphisms of
presheaves representable by algebraic spaces by testing the structure morphisms
of scheme Yoneda pullbacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An arbitrary represented Yoneda pullback with its actual projections.
The square has the universal property of the pullback; no chosen pullback
object is used to define this type of models. -/
structure PresheafRepresentedModel {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    {U : Over S} (ξ : yoneda.obj U ⟶ G) where
  space : AlgebraicSpace S
  hom : space ⟶ ofOver U
  fst : space.functorOfPoints ⟶ F
  isPullback : IsPullback fst hom a ξ

/-- Yoneda tests with all algebraic-space pullback models, without selecting one. -/
def presheafSpaceTests (S : Scheme.{u}) :
    MorphismProperty.TestFamily (AlgebraicSpace S) ((Over S)ᵒᵖ ⥤ Type u) where
  Test := fun {_ G} _ ↦ Σ U : Over S, yoneda.obj U ⟶ G
  Model := fun a t ↦ PresheafRepresentedModel a t.2
  projection := fun b ↦ Arrow.mk b.hom

/-- All-model representability agrees with the existing chosen-pullback predicate. -/
theorem presheafSpaceTests_representable_iff {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    (presheafSpaceTests S).representable a ↔ representableByAlgebraicSpaces a := by
  sorry

namespace representableByAlgebraicSpaces

/-- A morphism of presheaves representable by algebraic spaces has a morphism
property `P` of algebraic spaces when every scheme Yoneda pullback
`U ×_G F ⟶ U` has property `P`. -/
def has {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a)
    (P : MorphismProperty (AlgebraicSpace S)) : Prop :=
  ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), P (ha.pullbackHom ξ)

/-- A representable-by-algebraic-spaces morphism has property `P` if and only if
every scheme Yoneda pullback has property `P`. -/
theorem has_iff {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a)
    (P : MorphismProperty (AlgebraicSpace S)) :
    ha.has P ↔ ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), P (ha.pullbackHom ξ) :=
  sorry

/-- The chosen-pullback property agrees with testing every represented model
when `P` respects isomorphisms. Without this hypothesis an arbitrary property
can distinguish isomorphic pullback presentations. -/
theorem has_iff_presheafSpaceTests {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a)
    (P : MorphismProperty (AlgebraicSpace S)) [P.RespectsIso] :
    ha.has P ↔ (presheafSpaceTests S).has P a := by
  sorry

end representableByAlgebraicSpaces

/-- Transfer of a morphism property `P` of algebraic spaces over `S` to morphisms
of presheaves on `(Over S)ᵒᵖ`. A morphism `a : F ⟶ G` satisfies
`relativeAlgebraicSpaces P` when it is representable by algebraic spaces and
every scheme Yoneda pullback `U ×_G F ⟶ U` has property `P`.

The definition applies to arbitrary morphism properties; stability under base
change and fppf locality on the target are not assumptions of the definition. -/
def relativeAlgebraicSpaces {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) :
    MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
  fun _ _ a ↦ representableByAlgebraicSpaces a ∧
    ∀ (ha : representableByAlgebraicSpaces a), ha.has P

/-- A morphism of presheaves has the transferred property `P` if and only if it is
representable by algebraic spaces and every scheme Yoneda pullback has property
`P`. -/
theorem relativeAlgebraicSpaces_iff {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (P : MorphismProperty (AlgebraicSpace S)) :
    relativeAlgebraicSpaces P a ↔
      representableByAlgebraicSpaces a ∧
        ∀ (ha : representableByAlgebraicSpaces a) ⦃U : Over S⦄
          (ξ : yoneda.obj U ⟶ G), P (ha.pullbackHom ξ) :=
  sorry

/-- Compatibility view of the old predicate on chosen pullbacks as the generic
all-model relative property. The iso hypothesis is essential for this comparison,
but is not added to the old definition. -/
theorem relativeAlgebraicSpaces_iff_presheafSpaceTests {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (P : MorphismProperty (AlgebraicSpace S))
    [P.RespectsIso] (a : F ⟶ G) :
    relativeAlgebraicSpaces P a ↔ (presheafSpaceTests S).relative P a := by
  constructor
  · intro h
    exact ⟨(presheafSpaceTests_representable_iff a).mpr h.1,
      (h.1.has_iff_presheafSpaceTests P).mp (h.2 h.1)⟩
  · intro h
    have ha := (presheafSpaceTests_representable_iff a).mp h.1
    exact ⟨ha, fun ha' ↦ (ha'.has_iff_presheafSpaceTests P).mpr h.2⟩

namespace relativeAlgebraicSpaces

/-- A morphism representable by algebraic spaces whose scheme Yoneda pullbacks
have property `P` satisfies `relativeAlgebraicSpaces P`. -/
theorem of {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (P : MorphismProperty (AlgebraicSpace S))
    (ha : representableByAlgebraicSpaces a)
    (hP : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), P (ha.pullbackHom ξ)) :
    relativeAlgebraicSpaces P a :=
  sorry

/-- A morphism satisfying `relativeAlgebraicSpaces P` is representable by
algebraic spaces. -/
theorem representable {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    {P : MorphismProperty (AlgebraicSpace S)} (h : relativeAlgebraicSpaces P a) :
    representableByAlgebraicSpaces a :=
  sorry

/-- Scheme Yoneda pullbacks of a morphism satisfying `relativeAlgebraicSpaces P`
have property `P`. -/
theorem property_pullbackHom {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    {P : MorphismProperty (AlgebraicSpace S)} (h : relativeAlgebraicSpaces P a)
    ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G) :
    P ((representable h).pullbackHom ξ) :=
  sorry

end relativeAlgebraicSpaces

end AlgebraicGeometry.AlgebraicSpace
