/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Surjective morphisms of algebraic spaces

A morphism of algebraic spaces is surjective when the induced map of associated
point spaces is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is surjective if the induced map of associated
point spaces is surjective. -/
@[mk_iff]
class Surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The induced map on points is surjective. -/
  map_surjective : Function.Surjective (Points.map f)

namespace Surjective

/-- The identity morphism of an algebraic space is surjective. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Surjective (𝟙 X) :=
  ⟨fun x => ⟨x, Points.map_id x⟩⟩

/-- An isomorphism of algebraic spaces is surjective. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f] :
    Surjective f := by
  constructor
  intro y
  refine ⟨Points.map (inv f) y, ?_⟩
  rw [← Points.map_comp, IsIso.inv_hom_id, Points.map_id]

/-- A surjective morphism of algebraic spaces induces a surjective map of associated
point spaces. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Surjective f] :
    Function.Surjective (Points.map f) := Surjective.map_surjective

/-- A morphism of algebraic spaces is surjective as soon as the induced map of
associated point spaces is surjective. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Function.Surjective (Points.map f)) : Surjective f := ⟨hf⟩

end Surjective

/-- Surjectivity of morphisms of algebraic spaces is stable under composition. -/
instance surjective_isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Surjective S : MorphismProperty (AlgebraicSpace S)) where
  comp_mem f g hf hg := ⟨fun z => by
    obtain ⟨y, hy⟩ := hg.map_surjective z
    obtain ⟨x, hx⟩ := hf.map_surjective y
    exact ⟨x, by rw [Points.map_comp, hx, hy]⟩⟩

/-- The composition of surjective morphisms of algebraic spaces is surjective. -/
instance surjective_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Surjective g] :
    Surjective (f ≫ g) :=
  MorphismProperty.comp_mem (@Surjective S) f g inferInstance inferInstance

/-- A morphism from a scheme to an algebraic space has surjective represented base
changes if and only if its induced map on points is surjective. -/
theorem ofOver_presheaf_surjective_iff {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S}
    (f : ofOver T ⟶ X) :
    (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f ↔
      Function.Surjective (Points.map f) :=
  sorry

/-- A morphism from a scheme to an algebraic space with surjective represented base
changes induces a surjective map on points. -/
theorem ofOver_presheaf_surjective {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S}
    {f : ofOver T ⟶ X} (hf : (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f) :
    Function.Surjective (Points.map f) :=
  (ofOver_presheaf_surjective_iff f).mp hf

/-- A morphism from a scheme to an algebraic space whose induced map on points is
surjective has surjective represented base changes. -/
theorem ofOver_presheaf_surjective_of_map {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S}
    {f : ofOver T ⟶ X} (hf : Function.Surjective (Points.map f)) :
    (MorphismProperty.over (@AlgebraicGeometry.Surjective)).presheaf f :=
  (ofOver_presheaf_surjective_iff f).mpr hf

/-- A representable morphism of algebraic spaces has surjective represented base
changes if and only if its induced map on points is surjective. -/
theorem surjective_presheaf_iff_map_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (MorphismProperty.over (@AlgebraicGeometry.Surjective :
      MorphismProperty Scheme.{u})).presheaf f ↔
      Function.Surjective (Points.map f) :=
  sorry

/-- A representable morphism of algebraic spaces has surjective represented base
changes if and only if it is surjective. -/
theorem surjective_presheaf_iff_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (MorphismProperty.over (@AlgebraicGeometry.Surjective :
      MorphismProperty Scheme.{u})).presheaf f ↔
      Surjective f :=
  (surjective_presheaf_iff_map_surjective hf).trans (surjective_iff f).symm

/-- A representable morphism of algebraic spaces with surjective represented base
changes is surjective. -/
theorem surjective_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (MorphismProperty.over (@AlgebraicGeometry.Surjective :
      MorphismProperty Scheme.{u})).presheaf f) :
    Surjective f :=
  (surjective_presheaf_iff_surjective hf).mp h

/-- A representable surjective morphism of algebraic spaces has surjective
represented base changes. -/
theorem surjective_presheaf_of_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : Surjective f) :
    (MorphismProperty.over (@AlgebraicGeometry.Surjective :
      MorphismProperty Scheme.{u})).presheaf f :=
  (surjective_presheaf_iff_surjective hf).mpr h

end AlgebraicGeometry.AlgebraicSpace
