module

public import ReasLib.CategoryTheory.Bicategory.Comma.Map
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Identity
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Pseudofunctor

/-!
# Mapping pseudo comma bicategories

This leaf restricts colax comma mapping along a pseudofunctor to the
invertible-comparison pseudo comma bicategories.
-/

@[expose] public section

universe wA vA uA wB vB uB wC vC uC wD vD uD

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {D : Type uD} [Bicategory.{wD, vD} D]

namespace PseudoComma

variable {F : A ⥤ᵖ C} {G : B ⥤ᵖ C}

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

variable (F G) in
/-- The ambient induced target of pseudo comma mapping, before adding the
invertible-comparison membership witness. -/
private def ambientMap (H : C ⥤ᵖ D) :
    Pseudofunctor (PseudoComma F G)
      (InducedBicategory (ColaxComma (F.comp H) (G.comp H)) fun S ↦ S) :=
  ((ι F G).toPseudofunctor).comp
    ((ColaxComma.map F G H).comp
      (InducedBicategory.toInduced (ColaxComma (F.comp H) (G.comp H))).toPseudofunctor)

end Implementation

/-- Applying a pseudofunctor to a pseudo comma morphism preserves invertibility
of its structural comparison cell. -/
theorem map_mem (H : C ⥤ᵖ D) {S T : PseudoComma F G} (f : S ⟶ T) :
    IsIso (((ColaxComma.map F G H).map f.obj).cell) := sorry

variable (F G) in
/-- The induced ambient target of pseudo comma mapping satisfies the selected
invertible-comparison hom property. -/
private theorem ambientMap_mem (H : C ⥤ᵖ D)
    {S T : PseudoComma F G} (f : S ⟶ T) :
    IsIso (((Implementation.ambientMap F G H).map f).hom.cell) := sorry

variable (F G) in
/-- Apply a pseudofunctor to the structural arrows and invertible comparison
cells of a pseudo comma bicategory.

This is the locally induced lift of ColaxComma.map: it retains the mapped
comma objects and cells, and adds only the proof that the mapped comparison
cell is invertible.

The two comma legs are explicit because `H` does not determine the source
pseudo comma bicategory. -/
def map (H : C ⥤ᵖ D) :
    PseudoComma F G ⥤ᵖ PseudoComma (F.comp H) (G.comp H) :=
  LocallyInducedBicategory.liftPseudofunctor (Implementation.ambientMap F G H)
    (fun f ↦ ambientMap_mem F G H f)

/-- Mapping a pseudo comma bicategory commutes strictly with its left endpoint
projection.

The locally induced lift changes only the structural-arrow codomain and its
invertibility certificate, so both sides retain all left endpoint data. -/
theorem map.fst (H : C ⥤ᵖ D) :
    (map F G H).comp (fst (F.comp H) (G.comp H)) = fst F G := sorry

/-- Mapping a pseudo comma bicategory commutes strictly with its right endpoint
projection.

The locally induced lift changes only the structural-arrow codomain and its
invertibility certificate, so both sides retain all right endpoint data. -/
theorem map.snd (H : C ⥤ᵖ D) :
    (map F G H).comp (snd (F.comp H) (G.comp H)) = snd F G := sorry

/-- Pseudo comma mapping leaves the left endpoint object unchanged. -/
@[simp]
theorem map.obj.left (H : C ⥤ᵖ D) (S : PseudoComma F G) :
    ColaxComma.left ((map F G H).obj S) = ColaxComma.left S := sorry

/-- Pseudo comma mapping leaves the right endpoint object unchanged. -/
@[simp]
theorem map.obj.right (H : C ⥤ᵖ D) (S : PseudoComma F G) :
    ColaxComma.right ((map F G H).obj S) = ColaxComma.right S := sorry

/-- Pseudo comma mapping applies the pseudofunctor to the structural arrow. -/
@[simp]
theorem map.obj.hom (H : C ⥤ᵖ D) (S : PseudoComma F G) :
    ((map F G H).obj S).hom = H.map S.hom := sorry

/-- Pseudo comma mapping leaves the left endpoint map unchanged. -/
@[simp]
theorem map.hom.left (H : C ⥤ᵖ D) {S T : PseudoComma F G} (f : S ⟶ T) :
    left ((map F G H).map f) = left f := sorry

/-- Pseudo comma mapping leaves the right endpoint map unchanged. -/
@[simp]
theorem map.hom.right (H : C ⥤ᵖ D) {S T : PseudoComma F G} (f : S ⟶ T) :
    right ((map F G H).map f) = right f := sorry

/-- The selected comparison cell of a mapped pseudo comma morphism is the
mapped original cell surrounded by the composition comparisons of H. -/
@[simp]
theorem map.hom.cell (H : C ⥤ᵖ D) {S T : PseudoComma F G} (f : S ⟶ T) :
    PseudoComma.cell ((map F G H).map f) =
      (H.mapComp (F.map (PseudoComma.left f)) T.hom).inv ≫
        H.map₂ (PseudoComma.cell f) ≫
          (H.mapComp S.hom (G.map (PseudoComma.right f))).hom := sorry

/-- The forward selected comparison isomorphism of a mapped pseudo comma
morphism is its explicit mapped comparison cell. -/
@[simp]
theorem map.cellIso.hom (H : C ⥤ᵖ D) {S T : PseudoComma F G}
    (f : S ⟶ T) :
    (PseudoComma.cellIso ((map F G H).map f)).hom =
      (H.mapComp (F.map (PseudoComma.left f)) T.hom).inv ≫
        H.map₂ (PseudoComma.cell f) ≫
          (H.mapComp S.hom (G.map (PseudoComma.right f))).hom := sorry

/-- The inverse selected comparison isomorphism of a mapped pseudo comma
morphism is the reverse composite of the mapped original inverse comparison
and the two composition comparisons of H. -/
@[simp]
theorem map.cellIso.inv (H : C ⥤ᵖ D) {S T : PseudoComma F G}
    (f : S ⟶ T) :
    (PseudoComma.cellIso ((map F G H).map f)).inv =
      (H.mapComp S.hom (G.map (PseudoComma.right f))).inv ≫
        H.map₂ (PseudoComma.cellIso f).inv ≫
          (H.mapComp (F.map (PseudoComma.left f)) T.hom).hom := sorry

/-- Pseudo comma mapping leaves the left endpoint cell unchanged. -/
@[simp]
theorem map.map₂.left (H : C ⥤ᵖ D) {S T : PseudoComma F G}
    {f g : S ⟶ T} (η : f ⟶ g) :
    left₂ ((map F G H).map₂ η) = left₂ η := sorry

/-- Pseudo comma mapping leaves the right endpoint cell unchanged. -/
@[simp]
theorem map.map₂.right (H : C ⥤ᵖ D) {S T : PseudoComma F G}
    {f g : S ⟶ T} (η : f ⟶ g) :
    right₂ ((map F G H).map₂ η) = right₂ η := sorry

/-- The forward identity comparison of pseudo comma mapping is identity on the
left endpoint. -/
@[simp]
theorem map.mapId.hom.left (H : C ⥤ᵖ D) (S : PseudoComma F G) :
    left₂ ((map F G H).mapId S).hom = 𝟙 (𝟙 (ColaxComma.left S)) := sorry

/-- The forward identity comparison of pseudo comma mapping is identity on the
right endpoint. -/
@[simp]
theorem map.mapId.hom.right (H : C ⥤ᵖ D) (S : PseudoComma F G) :
    right₂ ((map F G H).mapId S).hom = 𝟙 (𝟙 (ColaxComma.right S)) := sorry

/-- The inverse identity comparison of pseudo comma mapping is identity on the
left endpoint. -/
@[simp]
theorem map.mapId.inv.left (H : C ⥤ᵖ D) (S : PseudoComma F G) :
    left₂ ((map F G H).mapId S).inv = 𝟙 (𝟙 (ColaxComma.left S)) := sorry

/-- The inverse identity comparison of pseudo comma mapping is identity on the
right endpoint. -/
@[simp]
theorem map.mapId.inv.right (H : C ⥤ᵖ D) (S : PseudoComma F G) :
    right₂ ((map F G H).mapId S).inv = 𝟙 (𝟙 (ColaxComma.right S)) := sorry

/-- The forward composition comparison of pseudo comma mapping is identity on
the left endpoint. -/
@[simp]
theorem map.mapComp.hom.left (H : C ⥤ᵖ D)
    {S T U : PseudoComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    left₂ ((map F G H).mapComp f g).hom = 𝟙 (left f ≫ left g) := sorry

/-- The forward composition comparison of pseudo comma mapping is identity on
the right endpoint. -/
@[simp]
theorem map.mapComp.hom.right (H : C ⥤ᵖ D)
    {S T U : PseudoComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    right₂ ((map F G H).mapComp f g).hom = 𝟙 (right f ≫ right g) := sorry

/-- The inverse composition comparison of pseudo comma mapping is identity on
the left endpoint. -/
@[simp]
theorem map.mapComp.inv.left (H : C ⥤ᵖ D)
    {S T U : PseudoComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    left₂ ((map F G H).mapComp f g).inv = 𝟙 (left f ≫ left g) := sorry

/-- The inverse composition comparison of pseudo comma mapping is identity on
the right endpoint. -/
@[simp]
theorem map.mapComp.inv.right (H : C ⥤ᵖ D)
    {S T U : PseudoComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    right₂ ((map F G H).mapComp f g).inv = 𝟙 (right f ≫ right g) := sorry

end PseudoComma

end Bicategory

end CategoryTheory
