/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A cartesian section of a functor `p : C ⥤ D` is a section functor whose image
of every morphism is strongly cartesian over its image in the base. -/
structure IsCartesianSection (p : C ⥤ D) (σ : D ⥤ C) : Prop where
  /-- The section functor projects to the identity on the base category. -/
  comm : σ ⋙ p = 𝟭 D
  /-- Every morphism in the section is strongly cartesian over its base morphism. -/
  map_isStronglyCartesian :
    ∀ {U V : D} (f : U ⟶ V), p.IsStronglyCartesian f (σ.map f)

/-- Construct a cartesian section from a section functor, its projection identity,
and its strong-cartesianness condition. -/
def IsCartesianSection.of (p : C ⥤ D) (σ : D ⥤ C) (comm : σ ⋙ p = 𝟭 D)
    (map_isStronglyCartesian :
      ∀ {U V : D} (f : U ⟶ V), p.IsStronglyCartesian f (σ.map f)) :
    IsCartesianSection p σ :=
  { comm := comm
    map_isStronglyCartesian := map_isStronglyCartesian }

/-- The defining conditions of a cartesian section are its strict section
equation and the strong-cartesianness of every image morphism. -/
theorem IsCartesianSection.spec (p : C ⥤ D) (σ : D ⥤ C) (h : IsCartesianSection p σ) :
    σ ⋙ p = 𝟭 D ∧
      ∀ {U V : D} (f : U ⟶ V), p.IsStronglyCartesian f (σ.map f) := sorry

end Functor
end CategoryTheory
