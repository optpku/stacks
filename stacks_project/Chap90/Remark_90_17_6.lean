/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import stacks_project.Chap90.Lemma_90_17_5_Action
public import stacks_project.Chap90.Remark_90_12_5_TangentSpace
public import stacks_project.Chap90.Remark_90_17_6_LiftsMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of the tensor action on lifts

A morphism of deformation categories induces maps on lift classes and on the
acting modules `T F_x0 ⊗[k] I`, and the action of Lemma 90.17.5 is natural
for those maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open Functor Fiber ArtinianLocalAlgCat IsLocalRing BasedCategory
open scoped Bicategory TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.BasedFunctor

/-- The projection of `BasedCategory.ofFunctor r` inherits the deformation
category structure of `r`. -/
instance instIsDeformationCategory_ofFunctor_p
    {E : Type v} [Category.{w} E] (r : E ⥤ ArtinianLocalAlgCat Λ k)
    [IsDeformationCategory r] :
    IsDeformationCategory (BasedCategory.ofFunctor r).p :=
  inferInstanceAs (IsDeformationCategory r)

/-- Hom-lifts of `r` are hom-lifts of the projection of `ofFunctor r`. -/
instance instIsHomLift_ofFunctor_p {E : Type v} [Category.{w} E]
    {r : E ⥤ ArtinianLocalAlgCat Λ k} {R S : ArtinianLocalAlgCat Λ k}
    {a b : E} {f : R ⟶ S} {φ : a ⟶ b} [h : r.IsHomLift f φ] :
    (BasedCategory.ofFunctor r).p.IsHomLift f φ := h

/-- Strongly cocartesian arrows of `r` remain strongly cocartesian for the
projection of `ofFunctor r`. -/
instance instIsStronglyCocartesian_ofFunctor_p {E : Type v} [Category.{w} E]
    {r : E ⥤ ArtinianLocalAlgCat Λ k} {R S : ArtinianLocalAlgCat Λ k}
    {a b : E} {f : R ⟶ S} {φ : a ⟶ b} [h : r.IsStronglyCocartesian f φ] :
    (BasedCategory.ofFunctor r).p.IsStronglyCocartesian f φ := h

/-- The image of a residue pushforward `x ⟶ x0` under a based functor. -/
def mapResiduePushforward {A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) {x : p.Fiber A}
    {x0 : p.Fiber (residue Λ k)} (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0) :
    fiberInclusion.obj ((Φ.fiberFunctor A).obj x) ⟶ fiberInclusion.obj (objAt Φ x0) :=
  Φ.map ψ

/-- `mapResiduePushforward` is the underlying functor applied to the residue
pushforward. -/
theorem mapResiduePushforward_hom {A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) {x : p.Fiber A}
    {x0 : p.Fiber (residue Λ k)} (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0) :
    mapResiduePushforward Φ ψ = Φ.map ψ := sorry

/-- The image of a residue pushforward still lies over `toResidue A`. -/
instance instIsHomLift_mapResiduePushforward {A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    {x : p.Fiber A} {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] :
    (BasedCategory.ofFunctor q).p.IsHomLift (toResidue A)
      (mapResiduePushforward Φ ψ) :=
  preserves_isHomLift Φ (toResidue A) ψ

/-- The image of a strongly cocartesian residue pushforward is strongly
cocartesian when the target is cofibered in groupoids. -/
instance instIsStronglyCocartesian_mapResiduePushforward
    {A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    {x : p.Fiber A} {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [IsFibered.InGroupoids q.op] [p.IsStronglyCocartesian (toResidue A) ψ] :
    (BasedCategory.ofFunctor q).p.IsStronglyCocartesian (toResidue A)
      (mapResiduePushforward Φ ψ) := sorry

/-- The map `d_x0 Φ ⊗ id_I : T F_x0 ⊗[k] I ⟶ T G_{Φ(x0)} ⊗[k] I` induced by a
morphism of deformation categories. -/
def tangentTensorMap [IsDeformationCategory p] [IsDeformationCategory q]
    {A' A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x0 : p.Fiber (residue Λ k)) :
    tangentTensor f hI x0 →ₗ[k] tangentTensor f hI (objAt Φ x0) :=
  (differentialLinearMapAt Φ x0).rTensor (kerModule f hI)

/-- `tangentTensorMap` is right tensor of `differentialLinearMapAt` with the
kernel module. -/
theorem tangentTensorMap_apply [IsDeformationCategory p] [IsDeformationCategory q]
    {A' A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x0 : p.Fiber (residue Λ k)) (θ : tangentTensor f hI x0) :
    tangentTensorMap Φ f hI x0 θ =
      (differentialLinearMapAt Φ x0).rTensor (kerModule f hI) θ := sorry

/-- `tangentTensorMap` acts by `differentialLinearMapAt` on elementary tensors. -/
theorem tangentTensorMap_tmul [IsDeformationCategory p] [IsDeformationCategory q]
    {A' A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x0 : p.Fiber (residue Λ k)) (t : tangentSpaceAt p x0) (i : kerModule f hI) :
    tangentTensorMap Φ f hI x0 (t ⊗ₜ i) = differentialLinearMapAt Φ x0 t ⊗ₜ i :=
  sorry

/-- The Lemma 90.17.5 action on a lift class after applying `Φ`. -/
def liftsTensorVAdd_image [IsDeformationCategory p] [IsDeformationCategory q]
    {A' A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) (f : A' ⟶ A)
    (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : tangentTensor f hI (objAt Φ x0))
    (y : lifts (BasedCategory.ofFunctor q).p f ((Φ.fiberFunctor A).obj x)) :
    lifts (BasedCategory.ofFunctor q).p f ((Φ.fiberFunctor A).obj x) :=
  @liftsTensorVAdd Λ k _ _ _ _ _ (BasedCategory.ofFunctor q).obj _
    (BasedCategory.ofFunctor q).p A' A (instIsDeformationCategory_ofFunctor_p q)
    f hf hI ((Φ.fiberFunctor A).obj x) (objAt Φ x0) (mapResiduePushforward Φ ψ)
    (instIsHomLift_mapResiduePushforward Φ ψ)
    (instIsStronglyCocartesian_mapResiduePushforward Φ ψ) θ y

/-- `liftsTensorVAdd_image` is the Lemma 90.17.5 action at the image residue
pushforward. -/
theorem liftsTensorVAdd_image_eq [IsDeformationCategory p] [IsDeformationCategory q]
    {A' A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) (f : A' ⟶ A)
    (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : tangentTensor f hI (objAt Φ x0))
    (y : lifts (BasedCategory.ofFunctor q).p f ((Φ.fiberFunctor A).obj x)) :
    liftsTensorVAdd_image Φ f hf hI x ψ θ y =
      @liftsTensorVAdd Λ k _ _ _ _ _ (BasedCategory.ofFunctor q).obj _
        (BasedCategory.ofFunctor q).p A' A (instIsDeformationCategory_ofFunctor_p q)
        f hf hI ((Φ.fiberFunctor A).obj x) (objAt Φ x0) (mapResiduePushforward Φ ψ)
        (instIsHomLift_mapResiduePushforward Φ ψ)
        (instIsStronglyCocartesian_mapResiduePushforward Φ ψ) θ y :=
  sorry

/-- Remark 90.17.6 The action of Lemma 90.17.5 is functorial. If `Φ` is a
morphism of deformation categories, `f : A' ⟶ A` is a surjection whose kernel
`I` is annihilated by `m_{A'}`, and `x` is an object of `F(A)`, then `Φ`
induces vertical arrows making the square of `liftsTensorVAdd` commute. Source
`φ` is `liftsMap`, `dφ ⊗ id_I` is `tangentTensorMap` as `rTensor` of
`differentialLinearMapAt`, and `T F ⊗[k] I` is the slice form `tangentTensor`
of Lemma 90.17.5. -/
@[stacks 06JJ]
theorem liftsTensorVAdd_map [IsDeformationCategory p] [IsDeformationCategory q]
    {A' A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) (f : A' ⟶ A)
    (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A) {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : tangentTensor f hI x0) (x' : lifts p f x) :
    liftsMap Φ f x (liftsTensorVAdd f hf hI x ψ θ x') =
      liftsTensorVAdd_image Φ f hf hI x ψ (tangentTensorMap Φ f hI x0 θ)
        (liftsMap Φ f x x') :=
  sorry

end CategoryTheory.BasedFunctor
