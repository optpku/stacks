/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points

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
        Groupoids.Hom.Surjective a ∧ Groupoids.Hom.Surjective (a ≫ f) :=
  sorry

/-- A morphism of algebraic stacks is surjective if and only if its induced
map on associated points is surjective. -/
theorem surjective_iff_map_surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Surjective f ↔ Function.Surjective (Points.map f) :=
  sorry

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
    Surjective (𝟙 X) :=
  sorry

/-- A surjective morphism of algebraic stacks admits a scheme atlas of the
source that remains surjective after composition. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Surjective f] :
    ∃ (U : Over S) (a : GroupoidsOver.slice U ⟶ X),
      Groupoids.Hom.Surjective a ∧ Groupoids.Hom.Surjective (a ≫ f) :=
  sorry

/-- A 1-morphism of algebraic stacks which is surjective in the sense of
relative representability by algebraic spaces is surjective as a morphism of
algebraic stacks. -/
instance of_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Surjective f] : Surjective f :=
  sorry

/-- An isomorphism of algebraic stacks is surjective. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f] : Surjective f :=
  sorry

end Surjective

end AlgebraicGeometry.AlgebraicStack
