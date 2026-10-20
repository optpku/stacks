/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SmallEtaleComparison

/-!
# Lemma 96.10.1

If a category fibred in groupoids `X` over `(Sch/S)_fppf` is represented by an
algebraic space `F`, a chosen equivalence `e : F.toGroupoids ≌ X` induces a
continuous and cocontinuous functor `u : F_étale ⥤ X`, hence a morphism of
ringed sites `π_F` and a morphism of ringed topoi `i_F` with `π_F ∘ i_F = id`
and `π_{F,*} = i_F⁻¹`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory MorphismOfTopoiIn

universe u

variable {S : Scheme.{u}}
variable (F : AlgebraicSpace S) (X : GroupoidsOver S) (e : F.toGroupoids ≌ X)

/- Lemma 96.10.1: a representing equivalence induces a continuous and
cocontinuous functor from the small étale site to the associated étale site. -/
@[stacks 073M] #check
  (AlgebraicGeometry.GroupoidsOver.smallEtaleFunctor_isContinuous_isCocontinuous F X e :
    (smallEtaleFunctor F X e).IsContinuous
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology ∧
    (smallEtaleFunctor F X e).IsCocontinuous
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology)

/- Lemma 96.10.1 (2): `u` induces a morphism of ringed sites
`π_F : (X_étale, O_X) ⟶ (F_étale, O_F)`. -/
@[stacks 073M] #check (AlgebraicGeometry.GroupoidsOver.pi F X e :
    RingedSite.Hom (etaleRingedSite X) (AlgebraicSpace.ringedSite F))

variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X e).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F X e).op.HasPointwiseRightKanExtension P]
variable [(AlgebraicSpace.smallEtaleTopology F).HasSheafCompose (forget RingCat.{u})]
variable [X.etaleTopology.HasSheafCompose (forget RingCat.{u})]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor F X e).op]

/- Lemma 96.10.1 (3): `u` induces a morphism of ringed topoi
`i_F : (Sh(F_étale), O_F) ⟶ (Sh(X_étale), O_X)`. -/
@[stacks 073M] #check (AlgebraicGeometry.GroupoidsOver.inclusion F X e :
    RingedSite.ToposHom (AlgebraicSpace.ringedSite F) (etaleRingedSite X))

variable [HasWeakSheafify X.etaleTopology (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X e).op.HasLeftKanExtension P]

/- Lemma 96.10.1 (4): the composite `π_F ∘ i_F` admits an invertible comparison
with the identity, compatible with the structure sheaf. -/
@[stacks 073M] #check (AlgebraicGeometry.GroupoidsOver.pi_comp_inclusion F X e :
    ∃ α : (RingedSite.ToposHom.comp (inclusion F X e) (piToposHom F X e)).toTopos.inverseImage ≅
        (RingedSite.ToposHom.id (AlgebraicSpace.ringedSite F)).toTopos.inverseImage,
      (RingedSite.ToposHom.comp (inclusion F X e) (piToposHom F X e)).structureMap =
        (MorphismOfTopoiIn.ringInverseImageNatIso α).hom.app
            (AlgebraicSpace.ringedSite F).structureSheaf ≫
          (RingedSite.ToposHom.id (AlgebraicSpace.ringedSite F)).structureMap)

/- Lemma 96.10.1 (5): `π_{F,*} = i_F⁻¹`. -/
@[stacks 073M] #check (AlgebraicGeometry.GroupoidsOver.pi_pushforward_eq_inclusion_inverseImage F X e :
    (piToposHom F X e).toTopos.pushforward =
      (inclusion F X e).toTopos.inverseImage)
