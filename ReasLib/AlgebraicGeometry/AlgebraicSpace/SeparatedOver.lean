/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-! # Algebraic spaces separated over a base -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
noncomputable section
universe u v
namespace AlgebraicGeometry.AlgebraicSpace

/-- The object property on `Over B` consisting of separated structure morphisms. -/
abbrev separatedMorphismOverProperty {S : Scheme.{u}} (B : AlgebraicSpace S) :
    ObjectProperty (Over B) := MorphismProperty.overObj (@Separated S)

/-- The full subcategory of algebraic spaces whose structure morphism to `B` is separated. -/
abbrev SeparatedMorphismOver {S : Scheme.{u}} (B : AlgebraicSpace S) : Type (u + 1) :=
  (separatedMorphismOverProperty B).FullSubcategory

namespace SeparatedMorphismOver
/-- The inclusion of the separated slice category into `Over B`. -/
abbrev inclusion {S : Scheme.{u}} (B : AlgebraicSpace S) :
    SeparatedMorphismOver B ⥤ Over B := (separatedMorphismOverProperty B).ι

/-- Objects of the separated slice category have separated structure morphisms. -/
instance instSeparated {S : Scheme.{u}} {B : AlgebraicSpace S}
    (Y : SeparatedMorphismOver B) : Separated Y.obj.hom := Y.property
end SeparatedMorphismOver

/-- Membership in the separated slice object property is separatedness of the structure map. -/
theorem separatedMorphismOverProperty_iff {S : Scheme.{u}} {B : AlgebraicSpace S} (Y : Over B) :
    separatedMorphismOverProperty B Y ↔ Separated Y.hom := sorry

variable {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A cocone is a colimit among separated objects when its legs induce unique maps to every
separated test object. -/
def IsColimitAmongSeparated {D : J ⥤ Over B} (c : Cocone D) : Prop :=
  ∀ (Z : Over B), Separated Z.hom → ∀ (s : D ⟶ (Functor.const J).obj Z),
    ∃! φ : c.pt ⟶ Z, ∀ i, c.ι.app i ≫ φ = s.app i

/-- The separated colimit predicate is its unique mapping-out specification. -/
theorem isColimitAmongSeparated_iff {D : J ⥤ Over B} (c : Cocone D) :
    IsColimitAmongSeparated c ↔
      ∀ (Z : Over B), Separated Z.hom → ∀ (s : D ⟶ (Functor.const J).obj Z),
        ∃! φ : c.pt ⟶ Z, ∀ i, c.ι.app i ≫ φ = s.app i := sorry

/-- A colimit in `Over B` is a colimit when tested against separated objects. -/
theorem isColimit_isColimitAmongSeparated {D : J ⥤ Over B} {c : Cocone D}
    (hc : IsColimit c) : IsColimitAmongSeparated c := sorry
end AlgebraicGeometry.AlgebraicSpace
