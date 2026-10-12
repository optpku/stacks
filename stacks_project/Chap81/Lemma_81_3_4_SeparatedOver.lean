/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap67.Definition_67_4_2_Separation

/-!
# Algebraic spaces separated over a base algebraic space

The full subcategory of `Over B` on separated structure morphisms, together with
the mapping-out property of a cocone among algebraic spaces separated over `B`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The object property on `Over B` consisting of separated structure morphisms. -/
abbrev separatedMorphismOverProperty {S : Scheme.{u}} (B : AlgebraicSpace S) :
    ObjectProperty (Over B) :=
  MorphismProperty.overObj (@Separated S)

/-- The full subcategory of algebraic spaces whose structure morphism to `B` is separated. -/
abbrev SeparatedMorphismOver {S : Scheme.{u}} (B : AlgebraicSpace S) : Type (u + 1) :=
  (separatedMorphismOverProperty B).FullSubcategory

namespace SeparatedMorphismOver

/-- The inclusion of algebraic spaces with separated structure morphism into all algebraic
spaces over `B`. -/
abbrev inclusion {S : Scheme.{u}} (B : AlgebraicSpace S) :
    SeparatedMorphismOver B ⥤ Over B :=
  (separatedMorphismOverProperty B).ι

/-- The structure morphism of an object of `SeparatedMorphismOver B` is separated. -/
instance instSeparated {S : Scheme.{u}} {B : AlgebraicSpace S}
    (Y : SeparatedMorphismOver B) : Separated Y.obj.hom :=
  Y.property

end SeparatedMorphismOver

/-- Membership in `separatedMorphismOverProperty B` is separatedness of the structure morphism. -/
theorem separatedMorphismOverProperty_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (Y : Over B) :
    separatedMorphismOverProperty B Y ↔ Separated Y.hom :=
  sorry

variable {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A cocone `c` is a colimit among algebraic spaces separated over `B` if it has unique
mapping-out against every test object `Z` over `B` with separated structure morphism. -/
def IsColimitAmongSeparated {D : J ⥤ Over B} (c : Cocone D) : Prop :=
  ∀ (Z : Over B), Separated Z.hom → ∀ (s : D ⟶ (Functor.const J).obj Z),
    ∃! φ : c.pt ⟶ Z, ∀ i, c.ι.app i ≫ φ = s.app i

/-- Unique mapping-out against separated-over-`B` test objects unpacks the colimit-among-separated
property. -/
theorem isColimitAmongSeparated_iff {D : J ⥤ Over B} (c : Cocone D) :
    IsColimitAmongSeparated c ↔
      ∀ (Z : Over B), Separated Z.hom → ∀ (s : D ⟶ (Functor.const J).obj Z),
        ∃! φ : c.pt ⟶ Z, ∀ i, c.ι.app i ≫ φ = s.app i :=
  sorry

/-- A colimit in `Over B` is in particular a colimit among algebraic spaces separated over `B`. -/
theorem isColimit_isColimitAmongSeparated {D : J ⥤ Over B} {c : Cocone D}
    (hc : IsColimit c) : IsColimitAmongSeparated c :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
