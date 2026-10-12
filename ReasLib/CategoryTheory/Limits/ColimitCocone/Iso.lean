/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.ColimitCocone.Morphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms between Explicit Colimit Cocones

An isomorphism of diagrams induces an isomorphism between the points of any explicitly supplied
colimit cocones. This leaf exposes the bundled construction and its leg, descent, identity,
symmetry, and composition computations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v v' u u'

namespace CategoryTheory.Limits.ColimitCocone

variable {J : Type u} [Category.{v} J]
variable {C : Type u'} [Category.{v'} C]

/-- The isomorphism between two explicit colimit cocone points induced by an isomorphism of
diagrams.

This is the bundled `ColimitCocone` interface to
`IsColimit.coconePointsIsoOfNatIso`. -/
@[stacks 002F "explicit colimit cocone isomorphism"]
def mapIso {F G : J ⥤ C} (P : ColimitCocone F) (Q : ColimitCocone G) (e : F ≅ G) :
    P.cocone.pt ≅ Q.cocone.pt :=
  IsColimit.coconePointsIsoOfNatIso P.isColimit Q.isColimit e

/-- The forward morphism of `mapIso` is the explicit-colimit map induced by `e.hom`. -/
@[simp]
theorem mapIso_hom {F G : J ⥤ C} (P : ColimitCocone F) (Q : ColimitCocone G)
    (e : F ≅ G) :
    (mapIso P Q e).hom = map P Q e.hom := sorry

/-- The inverse morphism of `mapIso` is the explicit-colimit map induced by `e.inv`. -/
@[simp]
theorem mapIso_inv {F G : J ⥤ C} (P : ColimitCocone F) (Q : ColimitCocone G)
    (e : F ≅ G) :
    (mapIso P Q e).inv = map Q P e.inv := sorry

/-- The forward morphism of `mapIso` has the expected composite with every source cocone leg. -/
@[reassoc (attr := simp)]
theorem ι_mapIso_hom {F G : J ⥤ C} (P : ColimitCocone F) (Q : ColimitCocone G)
    (e : F ≅ G) (j : J) :
    P.cocone.ι.app j ≫ (mapIso P Q e).hom = e.hom.app j ≫ Q.cocone.ι.app j := sorry

/-- The inverse morphism of `mapIso` has the expected composite with every target cocone leg. -/
@[reassoc (attr := simp)]
theorem ι_mapIso_inv {F G : J ⥤ C} (P : ColimitCocone F) (Q : ColimitCocone G)
    (e : F ≅ G) (j : J) :
    Q.cocone.ι.app j ≫ (mapIso P Q e).inv = e.inv.app j ≫ P.cocone.ι.app j := sorry

/-- The forward morphism of `mapIso` commutes with descent from the target colimit cocone. -/
@[reassoc]
theorem mapIso_hom_desc {F G : J ⥤ C} (P : ColimitCocone F) (Q : ColimitCocone G)
    (e : F ≅ G) (c : Cocone G) :
    (mapIso P Q e).hom ≫ Q.isColimit.desc c =
      P.isColimit.desc ((Cocone.precompose e.hom).obj c) := sorry

/-- The inverse morphism of `mapIso` commutes with descent from the source colimit cocone. -/
@[reassoc]
theorem mapIso_inv_desc {F G : J ⥤ C} (P : ColimitCocone F) (Q : ColimitCocone G)
    (e : F ≅ G) (c : Cocone F) :
    (mapIso P Q e).inv ≫ P.isColimit.desc c =
      Q.isColimit.desc ((Cocone.precompose e.inv).obj c) := sorry

/-- On colimit cocones selected by `HasColimit` instances, `mapIso` is Mathlib's
`HasColimit.isoOfNatIso`. -/
@[simp]
theorem mapIso_getColimitCocone {F G : J ⥤ C} [HasColimit F] [HasColimit G]
    (e : F ≅ G) :
    mapIso (getColimitCocone F) (getColimitCocone G) e = HasColimit.isoOfNatIso e := sorry

/-- The explicit-colimit isomorphism induced by the identity diagram isomorphism is the identity
isomorphism of the cocone point. -/
@[simp]
theorem mapIso_refl {F : J ⥤ C} (P : ColimitCocone F) :
    mapIso P P (Iso.refl F) = Iso.refl P.cocone.pt := sorry

/-- Reversing the diagram isomorphism reverses the induced explicit-colimit isomorphism. -/
@[simp]
theorem mapIso_symm {F G : J ⥤ C} (P : ColimitCocone F) (Q : ColimitCocone G)
    (e : F ≅ G) :
    (mapIso P Q e).symm = mapIso Q P e.symm := sorry

/-- Explicit-colimit isomorphisms respect transitivity of diagram isomorphisms. -/
theorem mapIso_trans {F G H : J ⥤ C}
    (P : ColimitCocone F) (Q : ColimitCocone G) (R : ColimitCocone H)
    (e : F ≅ G) (e' : G ≅ H) :
    mapIso P Q e ≪≫ mapIso Q R e' = mapIso P R (e ≪≫ e') := sorry

end CategoryTheory.Limits.ColimitCocone
