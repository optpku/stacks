/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Algebraic.Instances
public import ReasLib.Topology.Opens.SectionComparison
public import ReasLib.Topology.Sheaves.OpenCover.Basis
public import ReasLib.Topology.Sheaves.Basis.Comparison

/-!
# Algebraic gluing data on a subordinate basis

This module provides the basis-site sheaf attached to a `C`-valued open-family gluing datum when
`C` admits an algebraic forgetful functor to `Type`. The gluing datum itself is owned by
`TopCat.Sheaf.OpenCover.Gluing`; the cover hypothesis is used only to make the subordinate opens
a basis and to prove the resulting presheaf is a sheaf.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open TopologicalSpace.Opens
open TopCat.Opens.Subspace

noncomputable section

universe u v w

namespace TopCat.Sheaf.OpenCover.Gluing

variable {X : TopCat.{u}} {C : Type v} [Category.{u} C]
variable {ι : Type w} {U : ι → Opens X}

/-- After applying an algebraic forgetful functor, the basis presheaf of a gluing datum satisfies
the sheaf condition on the basis subordinate to an open cover. -/
theorem basisPresheaf_toType_isSheaf
    (F : C ⥤ Type u) [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U) :
    CategoryTheory.Presheaf.IsSheaf
      (basisGrothendieckTopology (TopologicalSpace.OpenCover.subordinateOpens U))
      (basisPresheaf data ⋙ F) := sorry

/-- The basis presheaf of an algebraic gluing datum is a sheaf on the basis subordinate to an
open cover. -/
theorem basisPresheaf_isSheaf
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U) :
    CategoryTheory.Presheaf.IsSheaf
      (basisGrothendieckTopology (TopologicalSpace.OpenCover.subordinateOpens U))
      (basisPresheaf data) := sorry

/-- The basis-site sheaf induced by an algebraic gluing datum on an open cover. -/
noncomputable def basisSheaf
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U) :
    BasisSiteSheaf C (TopologicalSpace.OpenCover.subordinateOpens U) where
  obj := basisPresheaf data
  property := basisPresheaf_isSheaf (F := F) data hU

/-- The ambient sheaf obtained by extending the basis sheaf associated to an algebraic gluing
datum. -/
noncomputable def basisSheafExtend
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U) : TopCat.Sheaf C X :=
  (basisSheaf (F := F) data hU).extend
    (TopologicalSpace.OpenCover.subordinateOpens_isBasis hU)

/-- The morphism of basis-site sheaves induced by a morphism of algebraic gluing data. -/
noncomputable def basisSheafHom
    {F : C ⥤ Type u} [IsAlgebraicStructure C F] (hU : IsOpenCover U)
    {A B : Gluing (C := C) U} (f : A ⟶ B) :
    basisSheaf (F := F) A hU ⟶ basisSheaf (F := F) B hU :=
  ObjectProperty.homMk (basisPresheafHom f)

/-- The basis-site sheaf morphism induced by an identity gluing morphism is the identity. -/
theorem basisSheafHom_id
    {F : C ⥤ Type u} [IsAlgebraicStructure C F] (hU : IsOpenCover U)
    (A : Gluing (C := C) U) :
    basisSheafHom (F := F) hU (𝟙 A) = 𝟙 (basisSheaf (F := F) A hU) := sorry

/-- The basis-site sheaf construction preserves composition of gluing morphisms. -/
theorem basisSheafHom_comp
    {F : C ⥤ Type u} [IsAlgebraicStructure C F] (hU : IsOpenCover U)
    {A B D : Gluing (C := C) U} (f : A ⟶ B) (g : B ⟶ D) :
    basisSheafHom (F := F) hU (f ≫ g) =
      basisSheafHom (F := F) hU f ≫ basisSheafHom (F := F) hU g := sorry

/-- The functor from algebraic gluing data on an open cover to sheaves on its subordinate basis. -/
noncomputable def basisSheafFunctor
    {F : C ⥤ Type u} [IsAlgebraicStructure C F] (hU : IsOpenCover U) :
    Gluing (C := C) U ⥤
      BasisSiteSheaf C (TopologicalSpace.OpenCover.subordinateOpens U) where
  obj := fun data ↦ basisSheaf (F := F) data hU
  map := basisSheafHom (F := F) hU
  map_id := basisSheafHom_id (F := F) hU
  map_comp := basisSheafHom_comp (F := F) hU

/-- The object of `basisSheafFunctor` is the basis-site sheaf associated to the gluing datum. -/
@[simp]
theorem basisSheafFunctor_obj
    {F : C ⥤ Type u} [IsAlgebraicStructure C F] (hU : IsOpenCover U)
    (data : Gluing (C := C) U) :
    (basisSheafFunctor (F := F) hU).obj data = basisSheaf (F := F) data hU := sorry

/-- The morphism of `basisSheafFunctor` is the basis-site sheaf morphism induced by gluing data. -/
@[simp]
theorem basisSheafFunctor_map
    {F : C ⥤ Type u} [IsAlgebraicStructure C F] (hU : IsOpenCover U)
    {A B : Gluing (C := C) U} (f : A ⟶ B) :
    (basisSheafFunctor (F := F) hU).map f = basisSheafHom (F := F) hU f := sorry

/-- The explicit realization functor from algebraic gluing data on an open cover to ambient
sheaves. -/
noncomputable def basisSheafExtendFunctor
    {F : C ⥤ Type u} [IsAlgebraicStructure C F] (hU : IsOpenCover U) :
    Gluing (C := C) U ⥤ TopCat.Sheaf C X :=
  basisSheafFunctor (F := F) hU ⋙
    BasisSiteSheaf.extendFunctor (C := C)
      (TopologicalSpace.OpenCover.subordinateOpens_isBasis hU)

/-- The object of the realization functor is the explicit extension of the associated basis
sheaf. -/
@[simp]
theorem basisSheafExtendFunctor_obj
    {F : C ⥤ Type u} [IsAlgebraicStructure C F] (hU : IsOpenCover U)
    (data : Gluing (C := C) U) :
    (basisSheafExtendFunctor (F := F) hU).obj data =
      basisSheafExtend (F := F) data hU := sorry

/-- The morphism of the realization functor is extension of the induced basis-site sheaf
morphism. -/
@[simp]
theorem basisSheafExtendFunctor_map
    {F : C ⥤ Type u} [IsAlgebraicStructure C F] (hU : IsOpenCover U)
    {A B : Gluing (C := C) U} (f : A ⟶ B) :
    (basisSheafExtendFunctor (F := F) hU).map f =
      (BasisSiteSheaf.extendFunctor (C := C)
        (TopologicalSpace.OpenCover.subordinateOpens_isBasis hU)).map
        (basisSheafHom (F := F) hU f) := sorry

namespace BasisRealization

/-- On an ambient open `W ⊆ U i`, restricting the extension of the basis sheaf of a gluing datum
recovers the section object of its `i`-th local sheaf. -/
noncomputable def sectionIso
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U)
    (i : ι) {W : Opens X} (hWi : W ≤ U i) :
    ((restrictToOpen (C := C) (U i)).obj
      (basisSheafExtend (F := F) data hU)).1.obj
        (op (subspaceOpenOfLE hWi)) ≅
      (data.localSheaf i).1.obj (op (subspaceOpenOfLE hWi)) :=
  let Wb : BasisOpen (TopologicalSpace.OpenCover.subordinateOpens U) := ⟨W, ⟨i, hWi⟩⟩
  (TopCat.Opens.Subspace.Section.iso
    (basisSheafExtend (F := F) data hU) hWi) ≪≫
    ((basisSheaf (F := F) data hU).restrictExtendIso
      (TopologicalSpace.OpenCover.subordinateOpens_isBasis hU)).symm.app
      (op Wb) ≪≫
    data.basisPresheafObjIso (op Wb) hWi

/-- The canonical chartwise section comparisons for the extension of a gluing datum commute with
restriction between represented opens. -/
@[reassoc]
theorem sectionIso_naturality
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U) (i : ι)
    {V W : Opens X} (hVW : V ≤ W) (hVi : V ≤ U i) (hWi : W ≤ U i) :
    ((restrictToOpen (C := C) (U i)).obj
      (basisSheafExtend (F := F) data hU)).1.map
        (subspaceOpenHom hVi hWi hVW).op ≫
      (sectionIso (F := F) data hU i hVi).hom =
    (sectionIso (F := F) data hU i hWi).hom ≫
      (data.localSheaf i).1.map (subspaceOpenHom hVi hWi hVW).op := sorry

/-- The chartwise section comparison, transported to an arbitrary open of the chart subspace. -/
noncomputable def componentIso
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U)
    (i : ι) (V : (Opens (space (U i)))ᵒᵖ) :
    ((restrictToOpen (C := C) (U i)).obj
      (basisSheafExtend (F := F) data hU)).1.obj V ≅
      (data.localSheaf i).1.obj V :=
  let hWi := ambientOpenOfSubspaceOpen_le V.unop
  let e := subspaceOpenOfAmbientOpenIso V.unop
  (((((restrictToOpen (C := C) (U i)).obj
      (basisSheafExtend (F := F) data hU)).1.mapIso e.op) ≪≫
    sectionIso (F := F) data hU i hWi) ≪≫
      ((data.localSheaf i).1.mapIso e.op).symm)

/-- The transported chartwise section comparisons are natural in opens of the chart subspace. -/
@[reassoc]
theorem componentIso_naturality
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U) (i : ι)
    {V W : (Opens (space (U i)))ᵒᵖ} (f : V ⟶ W) :
    ((restrictToOpen (C := C) (U i)).obj
      (basisSheafExtend (F := F) data hU)).1.map f ≫
        (componentIso (F := F) data hU i W).hom =
      (componentIso (F := F) data hU i V).hom ≫
        (data.localSheaf i).1.map f := sorry

/-- The underlying presheaf comparison between the restriction of the extended basis sheaf and
the local sheaf on a chart. -/
noncomputable def restrictionPresheafIso
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U) (i : ι) :
    ((restrictToOpen (C := C) (U i)).obj
      (basisSheafExtend (F := F) data hU)).1 ≅ (data.localSheaf i).1 :=
  NatIso.ofComponents (componentIso (F := F) data hU i)
    (componentIso_naturality (F := F) data hU i)

/-- Restricting the extension of the basis sheaf associated to a gluing datum to a chart recovers
the chart's local sheaf. -/
noncomputable def restrictionIso
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U) (i : ι) :
    (restrictToOpen (C := C) (U i)).obj
      (basisSheafExtend (F := F) data hU) ≅ data.localSheaf i :=
  ObjectProperty.isoMk
    (P := fun P => CategoryTheory.Presheaf.IsSheaf
      (Opens.grothendieckTopology (space (U i))) P)
    (restrictionPresheafIso (F := F) data hU i)

/-- The canonical chart comparisons for `basisSheafExtend` recover the prescribed overlap
isomorphisms of the original gluing datum. -/
theorem restrictionIso_compatible
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U) (i j : ι) :
    data.realizationLeftHom (basisSheafExtend (F := F) data hU)
        (fun k ↦ restrictionIso (F := F) data hU k) i j ≫
        (data.overlapIso i j).hom =
      data.realizationRightHom (basisSheafExtend (F := F) data hU)
        (fun k ↦ restrictionIso (F := F) data hU k) i j := sorry

/-- Extending the canonical basis-site sheaf realizes the algebraic gluing datum from which it
was constructed. Its chartwise comparisons are `restrictionIso`. -/
theorem realizes
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U) :
    data.Realizes (basisSheafExtend (F := F) data hU) := sorry

end BasisRealization

/-- Every algebraic open-cover gluing datum is realized by an ambient sheaf. -/
theorem existsRealizingSheaf
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (data : Gluing (C := C) U) (hU : IsOpenCover U) :
    ∃ sheaf : TopCat.Sheaf C X, data.Realizes sheaf := sorry

/-- Restriction from ambient sheaves is essentially surjective onto algebraic open-cover gluing
data. -/
theorem ofSheafFunctor_essSurj
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (hU : IsOpenCover U) :
    (ofSheafFunctor (C := C) U).EssSurj := sorry

/-- Restriction to an open cover is an equivalence for sheaves valued in algebraic structures. -/
theorem ofSheafFunctor_isEquivalence
    {F : C ⥤ Type u} [IsAlgebraicStructure C F]
    (hU : IsOpenCover U) :
    Functor.IsEquivalence (ofSheafFunctor (C := C) U) := sorry

end TopCat.Sheaf.OpenCover.Gluing
