/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap103.Lemma_103_14_2_Ringed
public import stacks_project.Chap103.«103_15_1_1_Map»

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.RingedMorphism

/-! Compatibility checks for restricted and ambient ringed-site morphisms.
The explicit existence hypotheses express the bounded-site size convention. -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor Opposite
open FiberedCategoryOver.Groupoids
open RingedSite.Cocontinuous
open scoped Bicategory MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap_comp_inclusion_op_hasPointwiseRightKanExtension_type :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Smooth f]
    (P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u)
    [(lisseEtaleInclusion X ⋙ toFunctor f).op.HasPointwiseRightKanExtension P],
    (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap_comp_inclusion_op_hasPointwiseRightKanExtension_type :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Flat f]
    (P : (flatFppfSite X)ᵒᵖ ⥤ Type u)
    [(flatFppfInclusion X ⋙ toFunctor f).op.HasPointwiseRightKanExtension P],
    (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P)

#check (AlgebraicGeometry.GroupoidsOver.toFunctor_isCocontinuous_etale :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    (toFunctor f).IsCocontinuous X.etaleTopology Y.etaleTopology)

#check (AlgebraicGeometry.GroupoidsOver.toFunctor_isCocontinuous_inheritedFppf :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    (toFunctor f).IsCocontinuous (inheritedFppfTopology X) (inheritedFppfTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInclusion_comp_toFunctor_isCocontinuous :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f],
    (lisseEtaleInclusion X ⋙ toFunctor f).IsCocontinuous
      (lisseEtaleTopology X) Y.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap_comp_inclusion_isCocontinuous :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f],
    (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).IsCocontinuous
      (lisseEtaleTopology X) Y.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInclusion_comp_toFunctor_isCocontinuous :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f],
    (flatFppfInclusion X ⋙ toFunctor f).IsCocontinuous
      (flatFppfTopology X) (inheritedFppfTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap_comp_inclusion_isCocontinuous :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f],
    (flatFppfMap f ⋙ flatFppfInclusion Y).IsCocontinuous
      (flatFppfTopology X) (inheritedFppfTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.etaleStructureSheafInverseImage :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleStructureSheaf Y) ⟶
      etaleStructureSheaf X)

#check (AlgebraicGeometry.AlgebraicStack.etaleStructureSheafInverseImage_eq :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    etaleStructureSheafInverseImage f =
      (inverseImageEtaleStructureSheafIso f).inv ≫
        CategoryTheory.Sheaf.ringSheafOfCommMap.{u, u + 1, u} (commEtaleStructureSheafIso f).hom)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap.structurePresheafHom :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f],
    (lisseEtaleMap f).op ⋙ (lisseEtaleStructureSheaf Y).obj ⟶
      (lisseEtaleStructureSheaf X).obj)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap.structurePresheafHom_eq :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f],
    lisseEtaleMap.structurePresheafHom f =
      whiskerRight (NatTrans.op (lisseEtaleMap_comp_ι f).inv)
          (etaleStructureSheaf Y).obj ≫
        whiskerLeft (lisseEtaleInclusion X).op
          (etaleStructureSheafInverseImage f).hom)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap.toposHom :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P],
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (lisseEtaleTopology Y) (lisseEtaleTopology X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap.toposHom_eq :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P],
    lisseEtaleMap.toposHom f =
      (lisseEtaleMap f).morphismOfTopoiInOfCocontinuous
        (lisseEtaleTopology X) (lisseEtaleTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap.ringedToposHom :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})],
    RingedSite.ToposHom (lisseEtaleRingedSite X) (lisseEtaleRingedSite Y))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap.ringedToposHom_toTopos :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f]
    [HasSheafify (lisseEtaleTopology X) (Type u)]
    [∀ P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u, (lisseEtaleMap f).op.HasPointwiseRightKanExtension P]
    [(lisseEtaleTopology X).HasSheafCompose (forget RingCat.{u})]
    [(lisseEtaleTopology Y).HasSheafCompose (forget RingCat.{u})],
    (lisseEtaleMap.ringedToposHom f).toTopos = lisseEtaleMap.toposHom f)

#check (AlgebraicGeometry.GroupoidsOver.toFunctor_isContinuous_inheritedFppf :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    (toFunctor f).IsContinuous (inheritedFppfTopology X) (inheritedFppfTopology Y))

#check (AlgebraicGeometry.GroupoidsOver.toFunctor_comp_p_isContinuous (τ := .fppf) :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    (toFunctor f ⋙ Y.p).IsContinuous
      (inheritedFppfTopology X) (Scheme.fppfTopology.over S))

#check (AlgebraicGeometry.GroupoidsOver.associatedStructureSheafInverseImageIso (τ := .fppf) :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        (inheritedFppfTopology X) (inheritedFppfTopology Y)).obj
      (structureSheaf Y) ≅ structureSheaf X)

#check (AlgebraicGeometry.GroupoidsOver.associatedStructureSheafInverseImageIso_eq (τ := .fppf) :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    associatedStructureSheafInverseImageIso f .fppf =
      (sheafPushforwardContinuousComp' (eqToIso (comm f)) RingCat.{u}
          (inheritedFppfTopology X) (inheritedFppfTopology Y)
          (Scheme.fppfTopology.over S)).app
        (StandardTopology.Big.structureSheaf .fppf S))

#check (AlgebraicGeometry.GroupoidsOver.associatedStructureSheafInverseImagePresheafHom (τ := .fppf) :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    (toFunctor f).op ⋙ (structureSheaf Y).obj ⟶ (structureSheaf X).obj)

#check (AlgebraicGeometry.GroupoidsOver.associatedStructureSheafInverseImagePresheafHom_eq (τ := .fppf) :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    associatedStructureSheafInverseImagePresheafHom f .fppf =
      (associatedStructureSheafInverseImageIso f .fppf).hom.hom)

#check (AlgebraicGeometry.AlgebraicStack.toFunctor.etaleToposHom :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P],
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u} Y.etaleTopology X.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.toFunctor.etaleToposHom_eq :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P],
    toFunctor.etaleToposHom f =
      (toFunctor f).morphismOfTopoiInOfCocontinuous X.etaleTopology Y.etaleTopology)

#check (AlgebraicGeometry.AlgebraicStack.toFunctor.etaleRingedToposHom :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    RingedSite.ToposHom (etaleRingedSite X) (etaleRingedSite Y))

#check (AlgebraicGeometry.AlgebraicStack.toFunctor.etaleRingedToposHom_toTopos :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [HasSheafify X.etaleTopology (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
    [Y.etaleTopology.HasSheafCompose (forget RingCat.{u})],
    (toFunctor.etaleRingedToposHom f).toTopos = toFunctor.etaleToposHom f)

#check (AlgebraicGeometry.AlgebraicStack.inheritedFppfToposHom :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P],
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (inheritedFppfTopology Y) (inheritedFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.inheritedFppfToposHom_eq :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P],
    inheritedFppfToposHom f =
      (toFunctor f).morphismOfTopoiInOfCocontinuous
        (inheritedFppfTopology X) (inheritedFppfTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.inheritedFppfRingedToposHom :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    RingedSite.ToposHom (ringedSite X) (ringedSite Y))

#check (AlgebraicGeometry.AlgebraicStack.inheritedFppfRingedToposHom_toTopos :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [HasSheafify (inheritedFppfTopology X) (Type u)]
    [∀ P : X.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
    [(inheritedFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(inheritedFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    (inheritedFppfRingedToposHom f).toTopos = inheritedFppfToposHom f)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap.structurePresheafHom :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f],
    (flatFppfMap f).op ⋙ (flatFppfStructureSheaf Y).obj ⟶
      (flatFppfStructureSheaf X).obj)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap.structurePresheafHom_eq :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f],
    flatFppfMap.structurePresheafHom f =
      whiskerRight (NatTrans.op (flatFppfMap_comp_ι f).inv) (structureSheaf Y).obj ≫
        whiskerLeft (flatFppfInclusion X).op (associatedStructureSheafInverseImagePresheafHom f .fppf))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap.toposHom :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P],
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (flatFppfTopology Y) (flatFppfTopology X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap.toposHom_eq :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P],
    flatFppfMap.toposHom f =
      (flatFppfMap f).morphismOfTopoiInOfCocontinuous
        (flatFppfTopology X) (flatFppfTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap.ringedToposHom :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    RingedSite.ToposHom (flatFppfRingedSite X) (flatFppfRingedSite Y))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap.ringedToposHom_toTopos :
  ∀ {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f]
    [HasSheafify (flatFppfTopology X) (Type u)]
    [∀ P : (flatFppfSite X)ᵒᵖ ⥤ Type u, (flatFppfMap f).op.HasPointwiseRightKanExtension P]
    [(flatFppfTopology X).HasSheafCompose (forget RingCat.{u})]
    [(flatFppfTopology Y).HasSheafCompose (forget RingCat.{u})],
    (flatFppfMap.ringedToposHom f).toTopos = flatFppfMap.toposHom f)

end AlgebraicGeometry.AlgebraicStack
