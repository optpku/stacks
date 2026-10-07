module

public import ReasLib.Topology.OpenCover.Basic
public import ReasLib.Topology.Opens.SectionComparison
public import ReasLib.Topology.Sheaves.OpenCover.Gluing
public import ReasLib.Topology.Sheaves.Basis.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover

/-!
# Basis presheaves from open-family gluing data

This module constructs the presheaf on opens subordinate to an indexed open family from
arbitrary `C`-valued local sheaves and their overlap identifications.  It is independent of any
algebraic forgetful functor and does not require the family to cover the ambient space; the cover
hypothesis is only needed when applying basis sheaf and descent results.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens
open TopCat.Presheaf.SheafCondition
open TopCat.Opens.Subspace TopCat.Opens.Subspace.Section

noncomputable section

universe u v w

namespace TopCat.Sheaf.OpenCover

variable {X : TopCat.{u}}
variable {C : Type v} [Category.{u} C]
variable {ι : Type w} {U : ι → Opens X}

namespace Gluing

/-- The section isomorphism supplied by a gluing datum between two charts over an open contained
in both charts. -/
noncomputable def overlapSectionIso (data : Gluing (C := C) U)
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j) :
    (data.localSheaf i).1.obj (op (subspaceOpenOfLE hWi)) ≅
      (data.localSheaf j).1.obj (op (subspaceOpenOfLE hWj)) :=
  let hWij : W ≤ U i ⊓ U j := le_inf hWi hWj
  let eLi := homOfLE_iso hWij inf_le_left (data.localSheaf i)
  let eRj := homOfLE_iso hWij inf_le_right (data.localSheaf j)
  eLi.symm ≪≫
    (((TopCat.Sheaf.forget C (space (U i ⊓ U j))).mapIso
      (data.overlapIso i j)).app (op (subspaceOpenOfLE hWij))) ≪≫
    eRj

/-- The forward map of `Gluing.overlapSectionIso` is restriction to the overlap, the prescribed
overlap map, and restriction to the target chart. -/
theorem overlapSectionIso_hom (data : Gluing (C := C) U)
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j) :
    (data.overlapSectionIso hWi hWj).hom =
      (homOfLE_iso
          (le_inf hWi hWj) inf_le_left (data.localSheaf i)).inv ≫
        (((TopCat.Sheaf.forget C (space (U i ⊓ U j))).mapIso
          (data.overlapIso i j)).hom.app
            (op (subspaceOpenOfLE (le_inf hWi hWj)))) ≫
        (homOfLE_iso
          (le_inf hWi hWj) inf_le_right (data.localSheaf j)).hom := sorry

/-- The overlap section isomorphisms of a gluing datum commute with restriction to a smaller
open. -/
@[reassoc]
theorem overlapSectionIso_naturality (data : Gluing (C := C) U)
    {V W : Opens X} {i j : ι}
    (hVW : V ≤ W) (hVi : V ≤ U i) (hVj : V ≤ U j)
    (hWi : W ≤ U i) (hWj : W ≤ U j) :
    (data.localSheaf i).1.map (subspaceOpenHom hVi hWi hVW).op ≫
      (data.overlapSectionIso hVi hVj).hom =
    (data.overlapSectionIso hWi hWj).hom ≫
      (data.localSheaf j).1.map (subspaceOpenHom hVj hWj hVW).op := sorry

/-- The object assigned to a subordinate basis open by the chosen-chart presheaf of a gluing
datum.

The chart used internally is deliberately hidden. Use `basisPresheafObjIso` to compare this
object with the section object of any chart containing the basis open. -/
noncomputable def basisPresheafObj (data : Gluing (C := C) U)
    (W : (BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U))ᵒᵖ) : C :=
  (data.localSheaf (OpensLeCover.index W.unop)).1.obj
    (op (subspaceOpenOfLE (OpensLeCover.homToIndex W.unop).down.down))

/-- The chosen-chart object of the basis presheaf is canonically isomorphic to the section
object in any chart containing the represented basis open. This is the public interface to the
hidden chart choice in `basisPresheafObj`. -/
noncomputable def basisPresheafObjIso (data : Gluing (C := C) U)
    (W : (BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U))ᵒᵖ)
    {i : ι} (hWi : W.unop.obj ≤ U i) :
    data.basisPresheafObj W ≅
      (data.localSheaf i).1.obj (op (subspaceOpenOfLE hWi)) :=
  data.overlapSectionIso (OpensLeCover.homToIndex W.unop).down.down hWi

/-- The restriction morphism of the chosen-chart basis presheaf of a gluing datum. -/
noncomputable def basisPresheafMap (data : Gluing (C := C) U)
    {V W : (BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U))ᵒᵖ} (f : V ⟶ W) :
    data.basisPresheafObj V ⟶ data.basisPresheafObj W :=
  let hWV : W.unop.obj ≤ V.unop.obj := f.unop.hom.le
  let hWcV : W.unop.obj ≤ U (OpensLeCover.index V.unop) :=
    hWV.trans (OpensLeCover.homToIndex V.unop).down.down
  (data.localSheaf (OpensLeCover.index V.unop)).1.map
      (subspaceOpenHom hWcV (OpensLeCover.homToIndex V.unop).down.down hWV).op ≫
    (data.overlapSectionIso hWcV (OpensLeCover.homToIndex W.unop).down.down).hom

/-- The restriction map of the basis presheaf is restriction in arbitrary source and target
charts, followed by the prescribed overlap transport and the inverse target comparison. -/
theorem basisPresheafMap_eq (data : Gluing (C := C) U)
    {V W : (BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U))ᵒᵖ} (f : V ⟶ W)
    {i j : ι} (hVi : V.unop.obj ≤ U i) (hWj : W.unop.obj ≤ U j) :
    data.basisPresheafMap f =
      (data.basisPresheafObjIso V hVi).hom ≫
        (data.localSheaf i).1.map
          (subspaceOpenHom (f.unop.hom.le.trans hVi) hVi f.unop.hom.le).op ≫
        (data.overlapSectionIso (f.unop.hom.le.trans hVi) hWj).hom ≫
          (data.basisPresheafObjIso W hWj).inv := sorry

/-- The chart comparisons of the basis presheaf commute with restriction between represented
basis opens. -/
theorem basisPresheafObjIso_naturality (data : Gluing (C := C) U)
    {V W : (BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U))ᵒᵖ} (f : V ⟶ W)
    {i j : ι} (hVi : V.unop.obj ≤ U i) (hWj : W.unop.obj ≤ U j) :
    (data.basisPresheafObjIso V hVi).hom ≫
        (data.localSheaf i).1.map
          (subspaceOpenHom (f.unop.hom.le.trans hVi) hVi f.unop.hom.le).op ≫
        (data.overlapSectionIso (f.unop.hom.le.trans hVi) hWj).hom =
      data.basisPresheafMap f ≫ (data.basisPresheafObjIso W hWj).hom := sorry

/-- The overlap section isomorphism of a gluing datum from a chart to itself is the identity. -/
@[simp]
theorem overlapSectionIso_self (data : Gluing (C := C) U)
    {W : Opens X} {i : ι} (hWi : W ≤ U i) :
    (data.overlapSectionIso hWi hWi).hom = 𝟙 _ := sorry

/-- Reversing the chart order in a gluing datum inverts the induced section isomorphism. -/
theorem overlapSectionIso_symm (data : Gluing (C := C) U)
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j) :
    data.overlapSectionIso hWi hWj = (data.overlapSectionIso hWj hWi).symm := sorry

/-- The overlap section isomorphisms of a gluing datum compose transitively on a common open. -/
@[simp, reassoc]
theorem overlapSectionIso_trans (data : Gluing (C := C) U)
    {W : Opens X} {i j k : ι}
    (hWi : W ≤ U i) (hWj : W ≤ U j) (hWk : W ≤ U k) :
    (data.overlapSectionIso hWi hWj).hom ≫
        (data.overlapSectionIso hWj hWk).hom =
      (data.overlapSectionIso hWi hWk).hom := sorry

/-- The chosen-chart basis restriction map sends identity inclusions to identities. -/
theorem basisPresheafMap_id (data : Gluing (C := C) U) :
    ∀ W : (BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U))ᵒᵖ,
      data.basisPresheafMap (𝟙 W) = 𝟙 _ := sorry

/-- The chosen-chart basis restriction map respects composition of inclusions. -/
theorem basisPresheafMap_comp (data : Gluing (C := C) U) :
    ∀ {A B D : (BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U))ᵒᵖ}
      (iAB : A ⟶ B) (iBD : B ⟶ D),
      data.basisPresheafMap (iAB ≫ iBD) =
        data.basisPresheafMap iAB ≫ data.basisPresheafMap iBD := sorry

/-- The `C`-valued presheaf on subordinate basis opens induced by a gluing datum. -/
noncomputable def basisPresheaf (data : Gluing (C := C) U) :
    (BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U))ᵒᵖ ⥤ C where
  obj W := data.basisPresheafObj W
  map f := data.basisPresheafMap f
  map_id := basisPresheafMap_id data
  map_comp := basisPresheafMap_comp data

/-- The component on a subordinate basis open induced by a morphism of gluing data.

The chosen chart is the one used by both source and target `basisPresheaf`; the chart choice is
therefore still hidden behind the basis-presheaf interface. -/
noncomputable def basisPresheafHomApp {A B : Gluing (C := C) U} (f : A ⟶ B)
    (W : (BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U))ᵒᵖ) :
    A.basisPresheafObj W ⟶ B.basisPresheafObj W :=
  (f.hom (OpensLeCover.index W.unop)).1.app
    (op (subspaceOpenOfLE (OpensLeCover.homToIndex W.unop).down.down))

/-- The basis-open components induced by a morphism of gluing data commute with restriction. -/
@[reassoc]
theorem basisPresheafHom_naturality {A B : Gluing (C := C) U} (f : A ⟶ B)
    {V W : (BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U))ᵒᵖ} (g : V ⟶ W) :
    A.basisPresheaf.map g ≫ basisPresheafHomApp f W =
      basisPresheafHomApp f V ≫ B.basisPresheaf.map g := sorry

/-- The morphism of subordinate-basis presheaves induced by a morphism of gluing data. -/
noncomputable def basisPresheafHom {A B : Gluing (C := C) U} (f : A ⟶ B) :
    A.basisPresheaf ⟶ B.basisPresheaf where
  app W := basisPresheafHomApp f W
  naturality := fun _ _ g ↦ basisPresheafHom_naturality f g

/-- The component of `basisPresheafHom` is the morphism of local sections on its chosen chart. -/
@[simp]
theorem basisPresheafHom_app {A B : Gluing (C := C) U} (f : A ⟶ B)
    (W : (BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U))ᵒᵖ) :
    (basisPresheafHom f).app W = basisPresheafHomApp f W := sorry

/-- The basis-presheaf morphism induced by an identity gluing morphism is the identity. -/
theorem basisPresheafHom_id (A : Gluing (C := C) U) :
    basisPresheafHom (𝟙 A) = 𝟙 A.basisPresheaf := sorry

/-- The basis-presheaf construction preserves composition of gluing morphisms. -/
theorem basisPresheafHom_comp {A B D : Gluing (C := C) U}
    (f : A ⟶ B) (g : B ⟶ D) :
    basisPresheafHom (f ≫ g) = basisPresheafHom f ≫ basisPresheafHom g := sorry

/-- The functor from open-family gluing data to presheaves on the subordinate basis. -/
noncomputable def basisPresheafFunctor :
    Gluing (C := C) U ⥤
      (BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U))ᵒᵖ ⥤ C where
  obj := basisPresheaf
  map := basisPresheafHom
  map_id := basisPresheafHom_id
  map_comp := basisPresheafHom_comp

/-- The object of `basisPresheafFunctor` is the basis presheaf of the gluing datum. -/
@[simp]
theorem basisPresheafFunctor_obj (data : Gluing (C := C) U) :
    (basisPresheafFunctor (C := C) (U := U)).obj data = basisPresheaf data := sorry

/-- The morphism of `basisPresheafFunctor` is induced by the corresponding gluing morphism. -/
@[simp]
theorem basisPresheafFunctor_map {A B : Gluing (C := C) U} (f : A ⟶ B) :
    (basisPresheafFunctor (C := C) (U := U)).map f = basisPresheafHom f := sorry

end Gluing

end TopCat.Sheaf.OpenCover
