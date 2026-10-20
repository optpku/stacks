/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoCone.Hom
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Postcomposition.Const

/-!
# Mapping conical pseudocones along a pseudofunctor

This module contains the data-level action of a pseudofunctor on arbitrary conical
pseudocones, their morphisms, and their `2`-morphisms.

Identity and composition comparisons and the resulting pseudofunctor are layered in downstream
transport modules. In particular, this neutral file has no dependency on pseudopullbacks or the
walking-cospan shape.
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
/-- Map an arbitrary conical pseudocone along a pseudofunctor. -/
def mapPseudoCone {E : Pseudofunctor J B} (K : Pseudofunctor B D)
    (s : Bicategory.PseudoCone E) : Bicategory.PseudoCone (E.comp K) :=
  Bicategory.PseudoCone.mk (K.obj s.pt)
    (mapConst J K s.pt ≫ (Pseudofunctor.postcomp J K).map s.π)

/-- The apex of a conical pseudocone mapped along a pseudofunctor. -/
@[simp]
theorem mapPseudoCone.pt {E : Pseudofunctor J B} (K : Pseudofunctor B D)
    (s : Bicategory.PseudoCone E) :
    (mapPseudoCone K s).pt = K.obj s.pt := sorry

/-- The strong transformation of a mapped conical pseudocone is the canonical constant-diagram
comparison followed by postcomposition of the original cone transformation. -/
@[simp]
theorem mapPseudoCone.π {E : Pseudofunctor J B} (K : Pseudofunctor B D)
    (s : Bicategory.PseudoCone E) :
    (mapPseudoCone K s).π =
      mapConst J K s.pt ≫ (Pseudofunctor.postcomp J K).map s.π := sorry

/-- The strong transformation of a mapped pseudocone, expressed using direct postcomposition
of the original cone transformation. -/
theorem mapPseudoCone.π_postcomp {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (s : Bicategory.PseudoCone E) :
    (mapPseudoCone K s).π = mapConst J K s.pt ≫ s.π.postcomp K := sorry

/-- The component of a mapped conical pseudocone is canonically isomorphic to the image of the
original component. The left unitor is essential in a non-strict bicategory. -/
def mapPseudoCone.appIso {E : Pseudofunctor J B} (K : Pseudofunctor B D)
    (s : Bicategory.PseudoCone E) (j : J) :
    (mapPseudoCone K s).π.app j ≅ K.map (s.π.app j) :=
  λ_ (K.map (s.π.app j))

/-- The forward map of the component comparison for a mapped pseudocone is the left unitor. -/
@[simp]
theorem mapPseudoCone.appIso.hom {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (s : Bicategory.PseudoCone E) (j : J) :
    (mapPseudoCone.appIso K s j).hom =
      (λ_ (K.map (s.π.app j))).hom := sorry

/-- The inverse map of the component comparison for a mapped pseudocone is the inverse left
unitor. -/
@[simp]
theorem mapPseudoCone.appIso.inv {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) (s : Bicategory.PseudoCone E) (j : J) :
    (mapPseudoCone.appIso K s j).inv =
      (λ_ (K.map (s.π.app j))).inv := sorry

namespace Implementation

/-- Postcompose the normalized comparison of a pseudocone morphism, first undoing the
postcomposition comparison for vertical composition. -/
private def mapPseudoCone.fac.postcomp {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T : Bicategory.PseudoCone E} (u : S ⟶ T) :
    StrongTrans.vcomp
        (((constDiagram J B).comp (Pseudofunctor.postcomp J K)).map
          (Bicategory.PseudoCone.map u))
        ((Pseudofunctor.postcomp J K).map T.π) ⟶
      (Pseudofunctor.postcomp J K).map S.π :=
  ((Pseudofunctor.postcomp J K).mapComp
      ((constDiagram J B).map (Bicategory.PseudoCone.map u)) T.π).inv ≫
    (Pseudofunctor.postcomp J K).map₂ (Bicategory.PseudoCone.fac u)

end Implementation

/-- The comparison modification carried by a mapped pseudocone morphism.

The first three factors use naturality of the constant-diagram comparison. The final two
factors compare postcomposition of a composite with the composite of the postcompositions,
then apply the image of the original cone comparison. -/
def mapPseudoCone.fac {E : Pseudofunctor J B} (K : Pseudofunctor B D)
    {S T : Bicategory.PseudoCone E} (u : S ⟶ T) :
    ((mapPseudoCone K T).comparison (K.obj S.pt)).obj
          (K.map (Bicategory.PseudoCone.map u)) ⟶
      (mapPseudoCone K S).π :=
  (α_ _ _ _).inv ≫
    (mapConst.transformation.naturalityIso J K
      (Bicategory.PseudoCone.map u)).hom ▷ (Pseudofunctor.postcomp J K).map T.π ≫
    (α_ _ _ _).hom ≫
    StrongTrans.whiskerLeft (mapConst J K S.pt)
      (Implementation.mapPseudoCone.fac.postcomp K u)

/-- Map a morphism of conical pseudocones along a pseudofunctor. Its apex map is the image of
the original apex map, and its comparison is `mapPseudoCone.fac`. -/
def mapPseudoCone.map {E : Pseudofunctor J B} (K : Pseudofunctor B D)
    {S T : Bicategory.PseudoCone E} (u : S ⟶ T) :
    mapPseudoCone K S ⟶ mapPseudoCone K T :=
  Bicategory.PseudoCone.homMk
    (K.map (Bicategory.PseudoCone.map u)) (mapPseudoCone.fac K u)

/-- The apex map of a mapped pseudocone morphism is the image of the original apex map. -/
@[simp]
theorem mapPseudoCone.map.apex {E : Pseudofunctor J B} (K : Pseudofunctor B D)
    {S T : Bicategory.PseudoCone E} (u : S ⟶ T) :
    Bicategory.PseudoCone.map (mapPseudoCone.map K u) =
      K.map (Bicategory.PseudoCone.map u) := sorry

/-- The comparison modification of a mapped pseudocone morphism is the explicitly assembled
mapped comparison. -/
@[simp]
theorem mapPseudoCone.map.fac {E : Pseudofunctor J B} (K : Pseudofunctor B D)
    {S T : Bicategory.PseudoCone E} (u : S ⟶ T) :
    Bicategory.PseudoCone.fac (mapPseudoCone.map K u) =
      mapPseudoCone.fac K u := sorry

namespace Implementation

/-- Compatibility of the mapped apex cell with the mapped comparison modifications. -/
private theorem mapPseudoCone.map₂.comm {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T : Bicategory.PseudoCone E}
    {u v : S ⟶ T} (η : u ⟶ v) :
    ((mapPseudoCone K T).comparison (K.obj S.pt)).map
          (K.map₂ (Bicategory.PseudoCone.map₂ η)) ≫
        Bicategory.PseudoCone.fac (mapPseudoCone.map K v) =
      Bicategory.PseudoCone.fac (mapPseudoCone.map K u) := sorry

end Implementation

/-- Map a `2`-morphism of conical pseudocones along a pseudofunctor. The underlying apex cell is
the image of the original apex cell. -/
def mapPseudoCone.map₂ {E : Pseudofunctor J B} (K : Pseudofunctor B D)
    {S T : Bicategory.PseudoCone E} {u v : S ⟶ T} (η : u ⟶ v) :
    mapPseudoCone.map K u ⟶ mapPseudoCone.map K v :=
  Bicategory.PseudoCone.hom₂Mk
    (K.map₂ (Bicategory.PseudoCone.map₂ η))
    (Implementation.mapPseudoCone.map₂.comm K η)

/-- The apex cell of a mapped pseudocone `2`-morphism is the image of the original apex cell. -/
@[simp]
theorem mapPseudoCone.map₂.apex {E : Pseudofunctor J B}
    (K : Pseudofunctor B D) {S T : Bicategory.PseudoCone E}
    {u v : S ⟶ T} (η : u ⟶ v) :
    Bicategory.PseudoCone.map₂ (mapPseudoCone.map₂ K η) =
      K.map₂ (Bicategory.PseudoCone.map₂ η) := sorry

/- Data audit (mathlib 4.32): `mapPseudoCone`, `mapPseudoCone.fac`,
`mapPseudoCone.map`, and `mapPseudoCone.map₂` report `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx`. Their apex, transformation, comparison, morphism, and `2`-cell
data are the explicit composites above. `sorryAx` is confined to inherited pseudofunctor and
strong-transformation coherence and the Prop-valued comparison compatibility field. -/

end Pseudofunctor

end CategoryTheory
