/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Surjective
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Diagonal

/-!
# Surjective morphisms of algebraic stacks

A morphism is surjective when a scheme atlas of its source remains surjective
after composition. This is equivalent to surjectivity on associated point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is surjective if some scheme atlas of the
source is surjective and remains surjective after composition. Equivalently,
the induced map of associated topological spaces is surjective. -/
class Surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop where
  /-- There is a scheme `U` over `S` and a surjective 1-morphism
  `a : GroupoidsOver.slice U ⟶ X` such that `a ≫ f` is also surjective. -/
  exists_surjective_scheme_atlas :
    ∃ (U : Over S) (a : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Surjective a ∧ Groupoids.Hom.Surjective (a ≫ f)

/-- A morphism of algebraic stacks is surjective if and only if some scheme
atlas of the source is surjective and remains surjective after composition. -/
theorem surjective_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Surjective f ↔
      ∃ (U : Over S) (a : GroupoidsOver.slice U ⟶ X),
        Groupoids.Hom.Surjective a ∧ Groupoids.Hom.Surjective (a ≫ f) := by
  exact ⟨fun h ↦ h.exists_surjective_scheme_atlas, fun h ↦ ⟨h⟩⟩

/-- A morphism of algebraic stacks is surjective if and only if its induced
map on associated points is surjective. -/
theorem surjective_iff_map_surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Surjective f ↔ Function.Surjective (Points.map f) := by
  constructor
  · rintro ⟨⟨U, a, ha, haf⟩⟩
    letI := haf
    intro y
    obtain ⟨x, hx⟩ := Groupoids.Hom.Surjective.map_surjective (a ≫ f) y
    exact ⟨Points.map a x, (Points.map_comp a f x).symm.trans hx⟩
  · intro hf
    obtain ⟨U, a, _, ha⟩ := AlgebraicStack.existsSmoothSurjectiveAtlas (X := X)
    letI := ha
    have hrep : relativelyRepresentableByAlgebraicSpaces (a ≫ f) :=
      (relativelyRepresentableByAlgebraicSpaces.diagonal_iff_slice Y).mp
        (AlgebraicStack.representableDiagonal (X := Y)) (a ≫ f)
    refine ⟨⟨U, a, ha, Groupoids.Hom.Surjective.of_map hrep ?_⟩⟩
    intro y
    obtain ⟨x, hx⟩ := hf y
    obtain ⟨z, hz⟩ := Groupoids.Hom.Surjective.map_surjective a x
    exact ⟨z, (Points.map_comp a f z).trans ((congrArg (Points.map f) hz).trans hx)⟩

namespace Surjective

/-- A surjective morphism of algebraic stacks induces a surjective map on
associated points. -/
theorem map_surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Surjective f] :
    Function.Surjective (Points.map f) :=
  (surjective_iff_map_surjective f).mp inferInstance

/-- A morphism of algebraic stacks is surjective whenever its induced map on
associated points is surjective. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : Function.Surjective (Points.map f)) : Surjective f :=
  (surjective_iff_map_surjective f).mpr hf

/-- The identity morphism of an algebraic stack is surjective. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Surjective (𝟙 X) := by
  obtain ⟨U, a, _, ha⟩ := AlgebraicStack.existsSmoothSurjectiveAtlas (X := X)
  refine ⟨⟨U, a, ha, ?_⟩⟩
  simpa only [Category.comp_id] using ha

/-- A surjective morphism of algebraic stacks admits a scheme atlas of the
source that remains surjective after composition. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Surjective f] :
    ∃ (U : Over S) (a : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Surjective a ∧ Groupoids.Hom.Surjective (a ≫ f) :=
  Surjective.exists_surjective_scheme_atlas (f := f)

/-- A 1-morphism of algebraic stacks which is surjective in the sense of
relative representability by algebraic spaces is surjective as a morphism of
algebraic stacks. -/
instance of_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Surjective f] : Surjective f :=
  (surjective_iff_map_surjective f).mpr (Groupoids.Hom.Surjective.map_surjective f)

/-- An isomorphism of algebraic stacks is surjective. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f] : Surjective f := by
  obtain ⟨g, _, hgf⟩ := (inferInstance : IsIso f).out
  apply of
  intro y
  refine ⟨Points.map g y, ?_⟩
  rw [← Points.map_comp, hgf, Points.map_id]

end Surjective

end AlgebraicGeometry.AlgebraicStack
