/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.KInjective.Displayed
public import ReasLib.CategoryTheory.DisplayedCategory.Total

/-!
# Total category of filtered K-injective resolutions

This leaf packages filtered K-injective resolutions over varying filtered complexes into their
canonical total category.  It exposes the source, resolving complex, and comparison as functorial
data without choosing any new resolution.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.KInjectiveResolution

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The total category of filtered complexes equipped with filtered K-injective resolutions. -/
@[stacks 0BKI "total category of filtered K-injective resolutions"]
abbrev Total (A : Type u) [Category.{v} A] [Abelian A] :=
  DisplayedCategory.Total (displayedCategory A)

namespace Total

/-- Forget a total filtered K-injective resolution to its source filtered complex. -/
@[stacks 0BKI "source of a total filtered K-injective resolution"]
abbrev source (A : Type u) [Category.{v} A] [Abelian A] :
    Total A ⥤ FilteredComplex A :=
  DisplayedCategory.Total.forget (displayedCategory A)

namespace Target

/-- The resolving-complex component of a total identity is the identity. -/
@[stacks 0BKI "identity law for total filtered K-injective targets"]
theorem mapId (X : Total A) :
    ((𝟙 X : X ⟶ X).displayed).hom = 𝟙 X.obj.complex := sorry

/-- The resolving-complex component of a total composite is the composite. -/
@[stacks 0BKI "composition law for total filtered K-injective targets"]
theorem mapComp {X Y Z : Total A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g).displayed).hom = f.displayed.hom ≫ g.displayed.hom := sorry

end Target

/-- Retain the resolving filtered complex of a total filtered K-injective resolution. -/
@[stacks 0BKI "target of a total filtered K-injective resolution"]
def target (A : Type u) [Category.{v} A] [Abelian A] :
    Total A ⥤ FilteredComplex A where
  obj X := X.obj.complex
  map f := f.displayed.hom
  map_id := Target.mapId
  map_comp := Target.mapComp

namespace Comparison

/-- The stored resolution maps make the total source-to-target comparisons natural. -/
@[stacks 0BKI "naturality of total filtered K-injective comparisons"]
theorem naturality {X Y : Total A} (f : X ⟶ Y) :
    (source A).map f ≫ Y.obj.ι = X.obj.ι ≫ (target A).map f := sorry

end Comparison

/-- The resolution comparisons form a natural transformation from sources to resolving
filtered complexes. -/
@[stacks 0BKI "comparison of total filtered K-injective resolutions"]
def comparison (A : Type u) [Category.{v} A] [Abelian A] :
    source A ⟶ target A where
  app X := X.obj.ι
  naturality _ _ f := Comparison.naturality f

/-- The source of a total filtered K-injective resolution is its stored base complex. -/
@[simp, stacks 0BKI "source of a total filtered K-injective resolution"]
theorem source_obj (X : Total A) : (source A).obj X = X.base := sorry

/-- The source functor sends a total resolution map to its stored base morphism. -/
@[simp, stacks 0BKI "source map of a total filtered K-injective resolution"]
theorem source_map {X Y : Total A} (f : X ⟶ Y) :
    (source A).map f = f.base := sorry

/-- The target of a total filtered K-injective resolution is its resolving complex. -/
@[simp, stacks 0BKI "target of a total filtered K-injective resolution"]
theorem target_obj (X : Total A) : (target A).obj X = X.obj.complex := sorry

/-- The target functor sends a total resolution map to its stored resolving-complex map. -/
@[simp, stacks 0BKI "target map of a total filtered K-injective resolution"]
theorem target_map {X Y : Total A} (f : X ⟶ Y) :
    (target A).map f = f.displayed.hom := sorry

/-- A component of the total comparison is the comparison stored by its resolution. -/
@[simp, stacks 0BKI "component of the total filtered K-injective comparison"]
theorem comparison_app (X : Total A) :
    (comparison A).app X = X.obj.ι := sorry

/-- Naturality of the total comparison, stated using the stored base and target maps. -/
@[reassoc, stacks 0BKI "naturality computation for total filtered K-injective comparisons"]
theorem comparison_naturality {X Y : Total A} (f : X ⟶ Y) :
    f.base ≫ Y.obj.ι = X.obj.ι ≫ f.displayed.hom := sorry

end Total

end CategoryTheory.FilteredComplex.KInjectiveResolution
