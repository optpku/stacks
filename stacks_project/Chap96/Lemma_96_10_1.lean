module

import StacksCheckRecall
public import stacks_project.Chap96.Lemma_96_10_1_Comparison

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

/-- Lemma 96.10.1 (1): there is a continuous and cocontinuous functor
`u : F_étale ⥤ X_étale` induced by a representing equivalence
`e : F.toGroupoids ≌ X`. -/
@[stacks 073M]
theorem AlgebraicGeometry.GroupoidsOver.smallEtaleFunctor_isContinuous_isCocontinuous :
    (smallEtaleFunctor F X e).IsContinuous
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology ∧
    (smallEtaleFunctor F X e).IsCocontinuous
      (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology :=
  sorry

/- Lemma 96.10.1 (2): `u` induces a morphism of ringed sites
`π_F : (X_étale, O_X) ⟶ (F_étale, O_F)`. -/
@[stacks 073M]
#check (pi F X e :
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
@[stacks 073M]
#check (inclusion F X e :
    RingedSite.ToposHom (AlgebraicSpace.ringedSite F) (etaleRingedSite X))

variable [HasWeakSheafify X.etaleTopology (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X e).op.HasLeftKanExtension P]

/- Lemma 96.10.1 (4): the composite `π_F ∘ i_F` is the identity on `Sh(F_étale)`. -/
@[stacks 073M]
#check (pi_comp_inclusion F X e :
    RingedSite.ToposHom.comp (inclusion F X e) (piToposHom F X e) =
      RingedSite.ToposHom.id (AlgebraicSpace.ringedSite F))

/- Lemma 96.10.1 (5): `π_{F,*} = i_F⁻¹`. -/
@[stacks 073M]
#check (pi_pushforward_eq_inclusion_inverseImage F X e :
    (piToposHom F X e).toTopos.pushforward =
      (inclusion F X e).toTopos.inverseImage)
