/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The full category of schemes over a Noetherian scheme `S` whose structure morphisms are
separated and of finite type. -/
abbrev FiniteTypeSeparatedOver (S : Scheme.{u}) [IsNoetherian S] :=
  ObjectProperty.FullSubcategory
    (fun X : Over S ↦ IsSeparated X.hom ∧ Hom.FiniteType X.hom)

namespace FiniteTypeSeparatedOver

variable {S : Scheme.{u}} [IsNoetherian S]

/-- The structure morphism of an object of `FiniteTypeSeparatedOver S` is separated. -/
instance instIsSeparated (X : FiniteTypeSeparatedOver S) : IsSeparated X.obj.hom :=
  X.property.1

/-- The structure morphism of an object of `FiniteTypeSeparatedOver S` is of finite type. -/
instance instFiniteType (X : FiniteTypeSeparatedOver S) : Hom.FiniteType X.obj.hom :=
  X.property.2

/-- The object condition in `FiniteTypeSeparatedOver S` is separatedness together with finite
type of the structure morphism. -/
theorem condition (X : FiniteTypeSeparatedOver S) :
    IsSeparated X.obj.hom ∧ Hom.FiniteType X.obj.hom := sorry

/-- Morphisms in `FiniteTypeSeparatedOver S` commute with the structure morphisms to `S`. -/
theorem hom_comm {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y) :
    f.hom.left ≫ Y.obj.hom = X.obj.hom := sorry

end FiniteTypeSeparatedOver

end AlgebraicGeometry.Scheme
