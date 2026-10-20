/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Basic

/-!
# Composition comparison for pseudocone transport

This module constructs the composition comparison for mapping arbitrary conical pseudocones
along a pseudofunctor. Its apex component is exactly the ambient pseudofunctor's `mapComp`.
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

namespace Implementation

/-- Compatibility of the forward composition comparison with the mapped cone comparisons. -/
private theorem mapPseudoCone.mapComp.hom.comm {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T U : Bicategory.PseudoCone E}
    (u : S ⟶ T) (v : T ⟶ U) :
    ((mapPseudoCone K U).comparison (K.obj S.pt)).map
          (K.mapComp (Bicategory.PseudoCone.map u)
            (Bicategory.PseudoCone.map v)).hom ≫
        Bicategory.PseudoCone.fac
          (mapPseudoCone.map K u ≫ mapPseudoCone.map K v) =
      Bicategory.PseudoCone.fac (mapPseudoCone.map K (u ≫ v)) := sorry

/-- The forward composition comparison between mapped pseudocone morphisms. -/
private def mapPseudoCone.mapComp.hom {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T U : Bicategory.PseudoCone E}
    (u : S ⟶ T) (v : T ⟶ U) :
    mapPseudoCone.map K (u ≫ v) ⟶
      mapPseudoCone.map K u ≫ mapPseudoCone.map K v :=
  Bicategory.PseudoCone.hom₂Mk
    (K.mapComp (Bicategory.PseudoCone.map u)
      (Bicategory.PseudoCone.map v)).hom
    (mapPseudoCone.mapComp.hom.comm K u v)

/-- Compatibility of the inverse composition comparison with the mapped cone comparisons. -/
private theorem mapPseudoCone.mapComp.inv.comm {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T U : Bicategory.PseudoCone E}
    (u : S ⟶ T) (v : T ⟶ U) :
    ((mapPseudoCone K U).comparison (K.obj S.pt)).map
          (K.mapComp (Bicategory.PseudoCone.map u)
            (Bicategory.PseudoCone.map v)).inv ≫
        Bicategory.PseudoCone.fac (mapPseudoCone.map K (u ≫ v)) =
      Bicategory.PseudoCone.fac
        (mapPseudoCone.map K u ≫ mapPseudoCone.map K v) := sorry

/-- The inverse composition comparison between mapped pseudocone morphisms. -/
private def mapPseudoCone.mapComp.inv {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T U : Bicategory.PseudoCone E}
    (u : S ⟶ T) (v : T ⟶ U) :
    mapPseudoCone.map K u ≫ mapPseudoCone.map K v ⟶
      mapPseudoCone.map K (u ≫ v) :=
  Bicategory.PseudoCone.hom₂Mk
    (K.mapComp (Bicategory.PseudoCone.map u)
      (Bicategory.PseudoCone.map v)).inv
    (mapPseudoCone.mapComp.inv.comm K u v)

/-- The forward and inverse composition comparisons cancel on the mapped composite. -/
private theorem mapPseudoCone.mapComp.homInvId {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T U : Bicategory.PseudoCone E}
    (u : S ⟶ T) (v : T ⟶ U) :
    mapPseudoCone.mapComp.hom K u v ≫ mapPseudoCone.mapComp.inv K u v =
      𝟙 (mapPseudoCone.map K (u ≫ v)) := sorry

/-- The inverse and forward composition comparisons cancel on the composite of mapped
pseudocone morphisms. -/
private theorem mapPseudoCone.mapComp.invHomId {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T U : Bicategory.PseudoCone E}
    (u : S ⟶ T) (v : T ⟶ U) :
    mapPseudoCone.mapComp.inv K u v ≫ mapPseudoCone.mapComp.hom K u v =
      𝟙 (mapPseudoCone.map K u ≫ mapPseudoCone.map K v) := sorry

end Implementation

/-- The composition comparison for mapping conical pseudocones along a pseudofunctor. Its apex
component is the composition comparison of the ambient pseudofunctor. -/
def mapPseudoCone.mapComp {E : Pseudofunctor J B} (K : Pseudofunctor B D)
    {S T U : Bicategory.PseudoCone E} (u : S ⟶ T) (v : T ⟶ U) :
    mapPseudoCone.map K (u ≫ v) ≅
      mapPseudoCone.map K u ≫ mapPseudoCone.map K v where
  hom := Implementation.mapPseudoCone.mapComp.hom K u v
  inv := Implementation.mapPseudoCone.mapComp.inv K u v
  hom_inv_id := Implementation.mapPseudoCone.mapComp.homInvId K u v
  inv_hom_id := Implementation.mapPseudoCone.mapComp.invHomId K u v

/-- The apex cell of the forward composition comparison is `K.mapComp`. -/
@[simp]
theorem mapPseudoCone.mapComp.hom.apex {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T U : Bicategory.PseudoCone E}
    (u : S ⟶ T) (v : T ⟶ U) :
    Bicategory.PseudoCone.map₂ (mapPseudoCone.mapComp K u v).hom =
      (K.mapComp (Bicategory.PseudoCone.map u)
        (Bicategory.PseudoCone.map v)).hom := sorry

/-- The apex cell of the inverse composition comparison is the inverse of `K.mapComp`. -/
@[simp]
theorem mapPseudoCone.mapComp.inv.apex {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T U : Bicategory.PseudoCone E}
    (u : S ⟶ T) (v : T ⟶ U) :
    Bicategory.PseudoCone.map₂ (mapPseudoCone.mapComp K u v).inv =
      (K.mapComp (Bicategory.PseudoCone.map u)
        (Bicategory.PseudoCone.map v)).inv := sorry

-- Data audit: the forward and inverse apex cells of `mapPseudoCone.mapComp` are respectively
-- `(K.mapComp _ _).hom` and `(K.mapComp _ _).inv`. Its `sorryAx` dependencies are confined to
-- compatibility, inverse-law, and computation propositions.

end Pseudofunctor

end CategoryTheory
