/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Displayed
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.Target
public import ReasLib.CategoryTheory.DisplayedCategory.Total

/-!
# Total Category of Strict Filtered-Injective Resolutions

This leaf packages strict filtered-injective resolutions into their canonical total category.
It exposes the source complex, the resolving complex with its termwise filtered-injective
property retained, and the bounded comparison as functorial data.  Every construction reads the
stored fields of the resolution and its displayed maps, so no resolution or comparison is chosen.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex.FilteredInjectivePlus.Resolution

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The total category of bounded-below complexes equipped with a strict filtered-injective
resolution. -/
@[stacks 05TW "total category of strict filtered-injective resolutions"]
abbrev Total (C : Type u) [Category.{v} C] [Abelian C] :=
  DisplayedCategory.Total (displayedCategory C)

namespace Total

/-- Forget a total strict filtered-injective resolution to its bounded-below source complex. -/
@[stacks 05TW "source of a total strict filtered-injective resolution"]
abbrev source (C : Type u) [Category.{v} C] [Abelian C] :
    Total C ⥤ CochainComplex.Plus (FilteredObject.Finite.category C) :=
  DisplayedCategory.Total.forget (displayedCategory C)

namespace Target

/-- The stored morphism of resolving complexes sends total identities to identities. -/
@[stacks 05TU "identity law for total strict-resolution targets"]
theorem mapId (X : Total C) :
    ((𝟙 X : X ⟶ X).displayed).complexMap = 𝟙 X.obj.complex := sorry

/-- The stored morphism of resolving complexes sends total composition to composition. -/
@[stacks 05TU "composition law for total strict-resolution targets"]
theorem mapComp {X Y Z : Total C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g).displayed).complexMap =
      f.displayed.complexMap ≫ g.displayed.complexMap := sorry

end Target

/-- Retain the termwise filtered-injective resolving complex of a total strict resolution. -/
@[stacks 05TW "termwise filtered-injective target of a total strict resolution"]
def target (C : Type u) [Category.{v} C] [Abelian C] :
    Total C ⥤ FilteredInjectivePlus C where
  obj X := X.obj.complex
  map f := f.displayed.complexMap
  map_id := Target.mapId
  map_comp := Target.mapComp

/-- Forget the termwise filtered-injective property while retaining the bounded-below target
complex of a total strict resolution. -/
@[stacks 05TW "bounded target complex of a total strict filtered-injective resolution"]
abbrev targetComplex (C : Type u) [Category.{v} C] [Abelian C] :
    Total C ⥤ CochainComplex.Plus (FilteredObject.Finite.category C) :=
  target C ⋙ ObjectProperty.ι _

namespace Comparison

/-- The stored comparison maps form a natural family from total sources to bounded resolving
complexes. -/
@[stacks 05TU "naturality of total strict-resolution comparisons"]
theorem naturality {X Y : Total C} (f : X ⟶ Y) :
    (source C).map f ≫ Y.obj.comparison =
      X.obj.comparison ≫ (targetComplex C).map f := sorry

end Comparison

/-- The bounded comparisons of strict filtered-injective resolutions form a natural
transformation on the total resolution category. -/
@[stacks 05TW "comparison of total strict filtered-injective resolutions"]
def comparison (C : Type u) [Category.{v} C] [Abelian C] :
    source C ⟶ targetComplex C where
  app X := X.obj.comparison
  naturality _ _ f := Comparison.naturality f

/-- The source of a total strict resolution is its stored base complex. -/
@[simp, stacks 05TW "source of a total strict filtered-injective resolution"]
theorem source_obj (X : Total C) : (source C).obj X = X.base := sorry

/-- The source functor sends a total resolution map to its stored base morphism. -/
@[simp, stacks 05TU "source map of a total strict filtered-injective resolution"]
theorem source_map {X Y : Total C} (f : X ⟶ Y) :
    (source C).map f = f.base := sorry

/-- The termwise filtered-injective target of a total resolution is its stored resolving
complex. -/
@[simp, stacks 05TW "termwise filtered-injective target of a total strict resolution"]
theorem target_obj (X : Total C) : (target C).obj X = X.obj.complex := sorry

/-- The target functor sends a total resolution map to its stored morphism of termwise
filtered-injective complexes. -/
@[simp, stacks 05TU "target map of a total strict filtered-injective resolution"]
theorem target_map {X Y : Total C} (f : X ⟶ Y) :
    (target C).map f = f.displayed.complexMap := sorry

/-- The bounded target complex of a total resolution is the bounded presentation of its stored
resolving complex. -/
@[simp, stacks 05TW "bounded target complex of a total strict filtered-injective resolution"]
theorem targetComplex_obj (X : Total C) :
    (targetComplex C).obj X = X.obj.target := sorry

/-- The bounded target-complex functor sends a total resolution map to its stored bounded target
map. -/
@[simp, stacks 05TU "bounded target map of a total strict filtered-injective resolution"]
theorem targetComplex_map {X Y : Total C} (f : X ⟶ Y) :
    (targetComplex C).map f = f.displayed.targetMap := sorry

/-- A component of the total comparison is the bounded comparison stored by its resolution. -/
@[simp, stacks 05TW "component of the total strict-resolution comparison"]
theorem comparison_app (X : Total C) :
    (comparison C).app X = X.obj.comparison := sorry

/-- Naturality of the total comparison, expressed entirely through the stored base and bounded
target maps. -/
@[reassoc, stacks 05TU "naturality computation for total strict-resolution comparisons"]
theorem comparison_naturality {X Y : Total C} (f : X ⟶ Y) :
    f.base ≫ Y.obj.comparison =
      X.obj.comparison ≫ f.displayed.targetMap := sorry

end Total

end CochainComplex.FilteredInjectivePlus.Resolution
