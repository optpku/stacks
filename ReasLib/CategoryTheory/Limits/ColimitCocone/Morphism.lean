/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms between Explicit Colimit Cocones

This leaf gives the bundled `ColimitCocone` interface to Mathlib's universal-property maps.
It applies to arbitrary diagram shapes and keeps the chosen colimit cocones explicit, without
requiring `HasColimit` instances or replacing them by globally selected colimits.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v v' u u'

namespace CategoryTheory.Limits.ColimitCocone

variable {J : Type u} [Category.{v} J]
variable {C : Type u'} [Category.{v'} C]

/-- The map between two explicit colimit cocone points induced by a natural transformation.

This is the bundled `ColimitCocone` interface to `IsColimit.map`. -/
@[stacks 002F "explicit colimit cocone map"]
def map {F G : J ⥤ C} (P : ColimitCocone F) (Q : ColimitCocone G) (f : F ⟶ G) :
    P.cocone.pt ⟶ Q.cocone.pt :=
  P.isColimit.map Q.cocone f

/-- An induced map of explicit colimit cocones has the expected composite with every source
cocone leg. -/
@[reassoc (attr := simp)]
theorem ι_map {F G : J ⥤ C} (P : ColimitCocone F) (Q : ColimitCocone G)
    (f : F ⟶ G) (j : J) :
    P.cocone.ι.app j ≫ map P Q f = f.app j ≫ Q.cocone.ι.app j := sorry

/-- Morphisms out of an explicit colimit cocone point are determined by their composites with
the cocone legs. -/
@[ext]
theorem hom_ext {F : J ⥤ C} (P : ColimitCocone F) {X : C}
    {f g : P.cocone.pt ⟶ X}
    (h : ∀ j : J, P.cocone.ι.app j ≫ f = P.cocone.ι.app j ≫ g) :
    f = g := sorry

/-- The map of explicit colimit cocones induced by the identity natural transformation is the
identity of the cocone point. -/
@[simp]
theorem map_id {F : J ⥤ C} (P : ColimitCocone F) :
    map P P (𝟙 F) = 𝟙 P.cocone.pt := sorry

/-- Maps between explicit colimit cocones respect composition of natural transformations. -/
@[reassoc]
theorem map_comp {F G H : J ⥤ C}
    (P : ColimitCocone F) (Q : ColimitCocone G) (R : ColimitCocone H)
    (f : F ⟶ G) (g : G ⟶ H) :
    map P Q f ≫ map Q R g = map P R (f ≫ g) := sorry

/-- Mapping to an explicit colimit cocone and then descending from it is descent from the source
after precomposition by the diagram morphism. -/
@[reassoc]
theorem map_desc {F G : J ⥤ C} (P : ColimitCocone F) (Q : ColimitCocone G)
    (f : F ⟶ G) (c : Cocone G) :
    map P Q f ≫ Q.isColimit.desc c =
      P.isColimit.desc ((Cocone.precompose f).obj c) := sorry

/-- For the colimit cocones selected by `HasColimit` instances, the explicit-cocone map is
Mathlib's `colimMap`. -/
@[simp]
theorem map_getColimitCocone {F G : J ⥤ C} [HasColimit F] [HasColimit G]
    (f : F ⟶ G) :
    map (getColimitCocone F) (getColimitCocone G) f = colimMap f := sorry

end CategoryTheory.Limits.ColimitCocone
