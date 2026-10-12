/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Pseudofunctor.Basic

/-!
# Computation API for pseudocone transport

This module exposes the projections of `mapPseudoCone.pseudofunctor` in the forms most useful
to downstream constructions. It keeps clients independent of the internal prelax and coherence
assembly.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uD vD wD uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} {D : Type uD}
variable [Bicategory.{wB, vB} B] [Bicategory.{wD, vD} D]
variable {J : Type uJ} [Bicategory.{wJ, vJ} J]

/-- The apex of an object transported by `mapPseudoCone.pseudofunctor`. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.obj.pt {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    ((mapPseudoCone.pseudofunctor K E).obj S).pt =
      K.obj S.pt := sorry

/-- The cone transformation of an object transported by `mapPseudoCone.pseudofunctor`. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.obj.π {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    ((mapPseudoCone.pseudofunctor K E).obj S).π =
      mapConst J K S.pt ≫ (postcomp J K).map S.π := sorry

/-- The transported cone transformation, expressed using direct postcomposition of the
original strong transformation. -/
theorem mapPseudoCone.pseudofunctor.obj.π_postcomp {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    ((mapPseudoCone.pseudofunctor K E).obj S).π =
      mapConst J K S.pt ≫ S.π.postcomp K := sorry

/-- Each component of a transported cone transformation is canonically isomorphic to the
image of the corresponding original component. -/
def mapPseudoCone.pseudofunctor.obj.appIso {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) (j : J) :
    ((mapPseudoCone.pseudofunctor K E).obj S).π.app j ≅
      K.map (S.π.app j) :=
  mapPseudoCone.appIso K S j

/-- The forward component of `mapPseudoCone.pseudofunctor.obj.appIso` is the left unitor. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.obj.appIso.hom {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) (j : J) :
    (mapPseudoCone.pseudofunctor.obj.appIso K S j).hom =
      (λ_ (K.map (S.π.app j))).hom := sorry

/-- The inverse component of `mapPseudoCone.pseudofunctor.obj.appIso` is the inverse left
unitor. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.obj.appIso.inv {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) (j : J) :
    (mapPseudoCone.pseudofunctor.obj.appIso K S j).inv =
      (λ_ (K.map (S.π.app j))).inv := sorry

/-- The apex map underlying the image of a pseudocone morphism. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.map.apex {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T : Bicategory.PseudoCone E} (u : S ⟶ T) :
    Bicategory.PseudoCone.map ((mapPseudoCone.pseudofunctor K E).map u) =
      K.map (Bicategory.PseudoCone.map u) := sorry

/-- The comparison modification underlying the image of a pseudocone morphism. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.map.fac {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T : Bicategory.PseudoCone E} (u : S ⟶ T) :
    Bicategory.PseudoCone.fac ((mapPseudoCone.pseudofunctor K E).map u) =
      mapPseudoCone.fac K u := sorry

/-- The apex cell underlying the image of a pseudocone `2`-morphism. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.map₂.apex {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T : Bicategory.PseudoCone E}
    {u v : S ⟶ T} (η : u ⟶ v) :
    Bicategory.PseudoCone.map₂ ((mapPseudoCone.pseudofunctor K E).map₂ η) =
      K.map₂ (Bicategory.PseudoCone.map₂ η) := sorry

/-- The forward unit comparison of pseudocone transport has apex cell `K.mapId`. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.mapId.hom.apex {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    Bicategory.PseudoCone.map₂
        ((mapPseudoCone.pseudofunctor K E).mapId S).hom =
      (K.mapId S.pt).hom := sorry

/-- The inverse unit comparison of pseudocone transport has the inverse apex cell of
`K.mapId`. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.mapId.inv.apex {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (S : Bicategory.PseudoCone E) :
    Bicategory.PseudoCone.map₂
        ((mapPseudoCone.pseudofunctor K E).mapId S).inv =
      (K.mapId S.pt).inv := sorry

/-- The forward composition comparison of pseudocone transport has apex cell `K.mapComp`. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.mapComp.hom.apex {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T U : Bicategory.PseudoCone E}
    (u : S ⟶ T) (v : T ⟶ U) :
    Bicategory.PseudoCone.map₂
        ((mapPseudoCone.pseudofunctor K E).mapComp u v).hom =
      (K.mapComp (Bicategory.PseudoCone.map u)
        (Bicategory.PseudoCone.map v)).hom := sorry

/-- The inverse composition comparison of pseudocone transport has the inverse apex cell of
`K.mapComp`. -/
@[simp]
theorem mapPseudoCone.pseudofunctor.mapComp.inv.apex {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T U : Bicategory.PseudoCone E}
    (u : S ⟶ T) (v : T ⟶ U) :
    Bicategory.PseudoCone.map₂
        ((mapPseudoCone.pseudofunctor K E).mapComp u v).inv =
      (K.mapComp (Bicategory.PseudoCone.map u)
        (Bicategory.PseudoCone.map v)).inv := sorry

-- Data audit: `mapPseudoCone.pseudofunctor.obj.appIso` is definitionally the explicit
-- `mapPseudoCone.appIso`, hence its morphisms are the left unitor and its inverse. Its inherited
-- `sorryAx` dependency comes from Prop-valued pseudofunctor coherence fields appearing in the
-- type of the transported object.

end Pseudofunctor

end CategoryTheory
