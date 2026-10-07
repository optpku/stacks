module

public import ReasLib.Algebra.Category.Ring.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap103.Lemma_103_14_2_Ringed
public import stacks_project.Chap103.«103_15_1_1_Map»

/-!
# Ringed morphisms induced by restricted lisse-étale and flat-fppf functors

A smooth (resp. flat) morphism of algebraic stacks induces a morphism of ringed
topoi on lisse-étale (resp. flat-fppf) sites, by the cocontinuous restricted
site functor together with the restricted identification of structure sheaves.
The associated-étale (resp. inherited-fppf) morphism of ringed topoi is the
unrestricted comparison edge of the functoriality square.
-/

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

/-- Pointwise right Kan extensions of type-valued presheaves along
`(toFunctor f).op`. -/
instance toFunctor_op_hasPointwiseRightKanExtension_type (f : X ⟶ Y)
    (P : X.totalᵒᵖ ⥤ Type u) :
    (toFunctor f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions of type-valued presheaves along
`(lisseEtaleMap f).op`. -/
instance lisseEtaleMap.op_hasPointwiseRightKanExtension_type
    (f : X ⟶ Y) [Smooth f] (P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u) :
    (lisseEtaleMap f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions of type-valued presheaves along
`(flatFppfMap f).op`. -/
instance flatFppfMap.op_hasPointwiseRightKanExtension_type
    (f : X ⟶ Y) [Flat f] (P : (flatFppfSite X)ᵒᵖ ⥤ Type u) :
    (flatFppfMap f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions of type-valued presheaves along the composite
of the lisse-étale inclusion of `X` with `toFunctor f`. -/
instance lisseEtaleInclusion_comp_toFunctor_op_hasPointwiseRightKanExtension_type
    (f : X ⟶ Y) [Smooth f]
    (P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u) :
    (lisseEtaleInclusion X ⋙ toFunctor f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions of type-valued presheaves along
`lisseEtaleMap f ⋙ lisseEtaleInclusion Y`. -/
instance lisseEtaleMap_comp_inclusion_op_hasPointwiseRightKanExtension_type
    (f : X ⟶ Y) [Smooth f]
    (P : (lisseEtaleSite X)ᵒᵖ ⥤ Type u) :
    (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).op.HasPointwiseRightKanExtension P :=
  HasPointwiseRightKanExtension.of_iso (NatIso.op (lisseEtaleMap_comp_ι f))
    (Iso.refl P)

/-- Pointwise right Kan extensions of type-valued presheaves along the composite
of the flat-fppf inclusion of `X` with `toFunctor f`. -/
instance flatFppfInclusion_comp_toFunctor_op_hasPointwiseRightKanExtension_type
    (f : X ⟶ Y) [Flat f]
    (P : (flatFppfSite X)ᵒᵖ ⥤ Type u) :
    (flatFppfInclusion X ⋙ toFunctor f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions of type-valued presheaves along
`flatFppfMap f ⋙ flatFppfInclusion Y`. -/
instance flatFppfMap_comp_inclusion_op_hasPointwiseRightKanExtension_type
    (f : X ⟶ Y) [Flat f]
    (P : (flatFppfSite X)ᵒᵖ ⥤ Type u) :
    (flatFppfMap f ⋙ flatFppfInclusion Y).op.HasPointwiseRightKanExtension P :=
  HasPointwiseRightKanExtension.of_iso (NatIso.op (flatFppfMap_comp_ι f))
    (Iso.refl P)

/-- The total functor of a 1-morphism is cocontinuous for associated étale
topologies. -/
instance toFunctor_isCocontinuous_etale (f : X ⟶ Y) :
    (toFunctor f).IsCocontinuous X.etaleTopology Y.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor f) (StandardTopology.etale.overTopology S)

/-- The total functor of a 1-morphism is cocontinuous for inherited fppf
topologies. -/
instance toFunctor_isCocontinuous_inheritedFppf (f : X ⟶ Y) :
    (toFunctor f).IsCocontinuous (inheritedFppfTopology X) (inheritedFppfTopology Y) :=
  CartesianBasedFunctor.inheritedTopology.isCocontinuous
    (toCartesianBasedFunctor f) (Scheme.fppfTopology.over S)

/-- The composite of a lisse-étale inclusion with a total functor is cocontinuous. -/
instance lisseEtaleInclusion_comp_toFunctor_isCocontinuous (f : X ⟶ Y) [Smooth f] :
    (lisseEtaleInclusion X ⋙ toFunctor f).IsCocontinuous
      (lisseEtaleTopology X) Y.etaleTopology :=
  isCocontinuous_comp (lisseEtaleInclusion X) (toFunctor f)
    (lisseEtaleTopology X) X.etaleTopology

/-- The composite `lisseEtaleMap f ⋙ lisseEtaleInclusion Y` is cocontinuous. -/
instance lisseEtaleMap_comp_inclusion_isCocontinuous (f : X ⟶ Y) [Smooth f] :
    (lisseEtaleMap f ⋙ lisseEtaleInclusion Y).IsCocontinuous
      (lisseEtaleTopology X) Y.etaleTopology :=
  isCocontinuous_comp (lisseEtaleMap f) (lisseEtaleInclusion Y)
    (lisseEtaleTopology X) (lisseEtaleTopology Y)

/-- The composite of a flat-fppf inclusion with a total functor is cocontinuous. -/
instance flatFppfInclusion_comp_toFunctor_isCocontinuous (f : X ⟶ Y) [Flat f] :
    (flatFppfInclusion X ⋙ toFunctor f).IsCocontinuous
      (flatFppfTopology X) (inheritedFppfTopology Y) :=
  isCocontinuous_comp (flatFppfInclusion X) (toFunctor f)
    (flatFppfTopology X) (inheritedFppfTopology X)

/-- The composite `flatFppfMap f ⋙ flatFppfInclusion Y` is cocontinuous. -/
instance flatFppfMap_comp_inclusion_isCocontinuous (f : X ⟶ Y) [Flat f] :
    (flatFppfMap f ⋙ flatFppfInclusion Y).IsCocontinuous
      (flatFppfTopology X) (inheritedFppfTopology Y) :=
  isCocontinuous_comp (flatFppfMap f) (flatFppfInclusion Y)
    (flatFppfTopology X) (flatFppfTopology Y)

/-- The identification `f⁻¹ 𝒪_Y ⟶ 𝒪_X` of étale structure sheaves, as the inverse
of the coefficient map `𝒪_X ⟶ f⁻¹ 𝒪_Y`. -/
def etaleStructureSheafInverseImage (f : X ⟶ Y) :
    ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleStructureSheaf Y) ⟶
      etaleStructureSheaf X :=
  (inverseImageEtaleStructureSheafIso f).inv ≫
    CategoryTheory.Sheaf.ringSheafOfCommMap.{u, u + 1, u} (commEtaleStructureSheafIso f).hom

/-- `etaleStructureSheafInverseImage` is the inverse-image form of
`commEtaleStructureSheafIso`. -/
theorem etaleStructureSheafInverseImage_eq (f : X ⟶ Y) :
    etaleStructureSheafInverseImage f =
      (inverseImageEtaleStructureSheafIso f).inv ≫
        CategoryTheory.Sheaf.ringSheafOfCommMap.{u, u + 1, u} (commEtaleStructureSheafIso f).hom :=
  sorry

/-- The structure-presheaf map of `lisseEtaleMap f`, obtained by restricting the
étale identification `f⁻¹ 𝒪_Y ⟶ 𝒪_X` along the lisse-étale inclusions. -/
def lisseEtaleMap.structurePresheafHom (f : X ⟶ Y) [Smooth f] :
    (lisseEtaleMap f).op ⋙ (lisseEtaleStructureSheaf Y).obj ⟶
      (lisseEtaleStructureSheaf X).obj :=
  whiskerRight (NatTrans.op (lisseEtaleMap_comp_ι f).inv) (etaleStructureSheaf Y).obj ≫
    whiskerLeft (lisseEtaleInclusion X).op (etaleStructureSheafInverseImage f).hom

/-- `lisseEtaleMap.structurePresheafHom` is restriction of
`etaleStructureSheafInverseImage` along the site square of `lisseEtaleMap`. -/
theorem lisseEtaleMap.structurePresheafHom_eq (f : X ⟶ Y) [Smooth f] :
    lisseEtaleMap.structurePresheafHom f =
      whiskerRight (NatTrans.op (lisseEtaleMap_comp_ι f).inv)
          (etaleStructureSheaf Y).obj ≫
        whiskerLeft (lisseEtaleInclusion X).op
          (etaleStructureSheafInverseImage f).hom :=
  sorry

/-- The morphism of topoi induced by the lisse-étale restriction of a smooth
morphism of algebraic stacks. -/
def lisseEtaleMap.toposHom (f : X ⟶ Y) [Smooth f] :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (lisseEtaleTopology Y) (lisseEtaleTopology X) :=
  (lisseEtaleMap f).morphismOfTopoiInOfCocontinuous
    (lisseEtaleTopology X) (lisseEtaleTopology Y)

/-- `lisseEtaleMap.toposHom` is the cocontinuous morphism of topoi of
`lisseEtaleMap f`. -/
theorem lisseEtaleMap.toposHom_eq (f : X ⟶ Y) [Smooth f] :
    lisseEtaleMap.toposHom f =
      (lisseEtaleMap f).morphismOfTopoiInOfCocontinuous
        (lisseEtaleTopology X) (lisseEtaleTopology Y) :=
  sorry

/-- The morphism of ringed topoi
`f' : Sh(X_lisse,étale) ⟶ Sh(Y_lisse,étale)` induced by a smooth morphism of
algebraic stacks. -/
def lisseEtaleMap.ringedToposHom (f : X ⟶ Y) [Smooth f] :
    RingedSite.ToposHom (lisseEtaleRingedSite X) (lisseEtaleRingedSite Y) :=
  @toRingedTopos.{u + 1, u, u + 1, u, u}
    (lisseEtaleRingedSite X) (lisseEtaleRingedSite Y) (lisseEtaleMap f)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (lisseEtaleMap.structurePresheafHom f)

/-- The underlying morphism of topoi of `lisseEtaleMap.ringedToposHom` is
`lisseEtaleMap.toposHom`. -/
theorem lisseEtaleMap.ringedToposHom_toTopos (f : X ⟶ Y) [Smooth f] :
    (lisseEtaleMap.ringedToposHom f).toTopos = lisseEtaleMap.toposHom f :=
  sorry

/-- The total functor of a 1-morphism is continuous for inherited fppf
topologies. -/
instance toFunctor_isContinuous_inheritedFppf (f : X ⟶ Y) :
    (toFunctor f).IsContinuous (inheritedFppfTopology X) (inheritedFppfTopology Y) :=
  CartesianBasedFunctor.inheritedTopology.isContinuous
    (toCartesianBasedFunctor f) (Scheme.fppfTopology.over S)

/-- The composite `toFunctor f ⋙ Y.p` is continuous from the inherited fppf
site of `X` to the big fppf site of `S`. -/
instance toFunctor_comp_p_isContinuous_inheritedFppf (f : X ⟶ Y) :
    (toFunctor f ⋙ Y.p).IsContinuous
      (inheritedFppfTopology X) (Scheme.fppfTopology.over S) :=
  Functor.isContinuous_comp (toFunctor f) Y.p
    (inheritedFppfTopology X) (inheritedFppfTopology Y)
    (Scheme.fppfTopology.over S)

/-- The identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` of inherited-fppf structure sheaves. -/
def inheritedFppfStructureSheafIso (f : X ⟶ Y) :
    ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        (inheritedFppfTopology X) (inheritedFppfTopology Y)).obj
      (structureSheaf Y) ≅ structureSheaf X :=
  (sheafPushforwardContinuousComp' (eqToIso (comm f)) RingCat.{u}
      (inheritedFppfTopology X) (inheritedFppfTopology Y)
      (Scheme.fppfTopology.over S)).app
    (StandardTopology.Big.structureSheaf .fppf S)

/-- `inheritedFppfStructureSheafIso` is the continuous-pushforward comparison
along `comm f`. -/
theorem inheritedFppfStructureSheafIso_eq (f : X ⟶ Y) :
    inheritedFppfStructureSheafIso f =
      (sheafPushforwardContinuousComp' (eqToIso (comm f)) RingCat.{u}
          (inheritedFppfTopology X) (inheritedFppfTopology Y)
          (Scheme.fppfTopology.over S)).app
        (StandardTopology.Big.structureSheaf .fppf S) :=
  sorry

/-- The structure-presheaf map of `toFunctor f` on inherited fppf ringed sites. -/
def inheritedFppfStructurePresheafHom (f : X ⟶ Y) :
    (toFunctor f).op ⋙ (structureSheaf Y).obj ⟶ (structureSheaf X).obj :=
  (inheritedFppfStructureSheafIso f).hom.hom

/-- `inheritedFppfStructurePresheafHom` is the underlying presheaf map of
`inheritedFppfStructureSheafIso`. -/
theorem inheritedFppfStructurePresheafHom_eq (f : X ⟶ Y) :
    inheritedFppfStructurePresheafHom f =
      (inheritedFppfStructureSheafIso f).hom.hom :=
  sorry

/-- The morphism of topoi induced by `toFunctor f` on associated étale sites. -/
def toFunctor.etaleToposHom (f : X ⟶ Y) :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u} Y.etaleTopology X.etaleTopology :=
  (toFunctor f).morphismOfTopoiInOfCocontinuous X.etaleTopology Y.etaleTopology

/-- `toFunctor.etaleToposHom` is the cocontinuous morphism of topoi of
`toFunctor f` on associated étale topologies. -/
theorem toFunctor.etaleToposHom_eq (f : X ⟶ Y) :
    toFunctor.etaleToposHom f =
      (toFunctor f).morphismOfTopoiInOfCocontinuous X.etaleTopology Y.etaleTopology :=
  sorry

/-- The morphism of associated-étale ringed topoi induced by a 1-morphism of
algebraic stacks, via `toFunctor f`. -/
def toFunctor.etaleRingedToposHom (f : X ⟶ Y) :
    RingedSite.ToposHom (etaleRingedSite X) (etaleRingedSite Y) :=
  @toRingedTopos.{u + 1, u, u + 1, u, u}
    (etaleRingedSite X) (etaleRingedSite Y) (toFunctor f)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (etaleStructureSheafInverseImage f).hom

/-- The underlying morphism of topoi of `toFunctor.etaleRingedToposHom` is
`toFunctor.etaleToposHom`. -/
theorem toFunctor.etaleRingedToposHom_toTopos (f : X ⟶ Y) :
    (toFunctor.etaleRingedToposHom f).toTopos = toFunctor.etaleToposHom f :=
  sorry

/-- The morphism of topoi induced by `toFunctor f` on inherited fppf sites. -/
def inheritedFppfToposHom (f : X ⟶ Y) :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (inheritedFppfTopology Y) (inheritedFppfTopology X) :=
  (toFunctor f).morphismOfTopoiInOfCocontinuous
    (inheritedFppfTopology X) (inheritedFppfTopology Y)

/-- `inheritedFppfToposHom` is the cocontinuous morphism of topoi of
`toFunctor f` on inherited fppf topologies. -/
theorem inheritedFppfToposHom_eq (f : X ⟶ Y) :
    inheritedFppfToposHom f =
      (toFunctor f).morphismOfTopoiInOfCocontinuous
        (inheritedFppfTopology X) (inheritedFppfTopology Y) :=
  sorry

/-- The morphism of inherited-fppf ringed topoi induced by a 1-morphism of
categories fibred in groupoids. -/
def inheritedFppfRingedToposHom (f : X ⟶ Y) :
    RingedSite.ToposHom (ringedSite X) (ringedSite Y) :=
  @toRingedTopos.{u + 1, u, u + 1, u, u}
    (ringedSite X) (ringedSite Y) (toFunctor f)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (inheritedFppfStructurePresheafHom f)

/-- The underlying morphism of topoi of `inheritedFppfRingedToposHom` is
`inheritedFppfToposHom`. -/
theorem inheritedFppfRingedToposHom_toTopos (f : X ⟶ Y) :
    (inheritedFppfRingedToposHom f).toTopos = inheritedFppfToposHom f :=
  sorry

/-- The structure-presheaf map of `flatFppfMap f`, obtained by restricting the
inherited-fppf identification `f⁻¹ 𝒪_Y ⟶ 𝒪_X` along the flat-fppf inclusions. -/
def flatFppfMap.structurePresheafHom (f : X ⟶ Y) [Flat f] :
    (flatFppfMap f).op ⋙ (flatFppfStructureSheaf Y).obj ⟶
      (flatFppfStructureSheaf X).obj :=
  whiskerRight (NatTrans.op (flatFppfMap_comp_ι f).inv) (structureSheaf Y).obj ≫
    whiskerLeft (flatFppfInclusion X).op (inheritedFppfStructurePresheafHom f)

/-- `flatFppfMap.structurePresheafHom` is restriction of
`inheritedFppfStructurePresheafHom` along the site square of `flatFppfMap`. -/
theorem flatFppfMap.structurePresheafHom_eq (f : X ⟶ Y) [Flat f] :
    flatFppfMap.structurePresheafHom f =
      whiskerRight (NatTrans.op (flatFppfMap_comp_ι f).inv) (structureSheaf Y).obj ≫
        whiskerLeft (flatFppfInclusion X).op (inheritedFppfStructurePresheafHom f) :=
  sorry

/-- The morphism of topoi induced by the flat-fppf restriction of a flat morphism
of algebraic stacks. -/
def flatFppfMap.toposHom (f : X ⟶ Y) [Flat f] :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      (flatFppfTopology Y) (flatFppfTopology X) :=
  (flatFppfMap f).morphismOfTopoiInOfCocontinuous
    (flatFppfTopology X) (flatFppfTopology Y)

/-- `flatFppfMap.toposHom` is the cocontinuous morphism of topoi of
`flatFppfMap f`. -/
theorem flatFppfMap.toposHom_eq (f : X ⟶ Y) [Flat f] :
    flatFppfMap.toposHom f =
      (flatFppfMap f).morphismOfTopoiInOfCocontinuous
        (flatFppfTopology X) (flatFppfTopology Y) :=
  sorry

/-- The morphism of ringed topoi
`f' : Sh(X_flat,fppf) ⟶ Sh(Y_flat,fppf)` induced by a flat morphism of
algebraic stacks. -/
def flatFppfMap.ringedToposHom (f : X ⟶ Y) [Flat f] :
    RingedSite.ToposHom (flatFppfRingedSite X) (flatFppfRingedSite Y) :=
  @toRingedTopos.{u + 1, u, u + 1, u, u}
    (flatFppfRingedSite X) (flatFppfRingedSite Y) (flatFppfMap f)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (flatFppfMap.structurePresheafHom f)

/-- The underlying morphism of topoi of `flatFppfMap.ringedToposHom` is
`flatFppfMap.toposHom`. -/
theorem flatFppfMap.ringedToposHom_toTopos (f : X ⟶ Y) [Flat f] :
    (flatFppfMap.ringedToposHom f).toTopos = flatFppfMap.toposHom f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
