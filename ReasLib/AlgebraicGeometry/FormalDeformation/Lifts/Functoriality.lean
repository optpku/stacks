module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import ReasLib.AlgebraicGeometry.FormalDeformation.Lifts.Torsor
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.At
public import ReasLib.CategoryTheory.Fibered.Lifts.Map

/-!
# Functoriality of the tensor action on lifts

A morphism of deformation categories induces maps on lift classes and on the
acting modules `T F_x0 ⊗[k] I`, and the canonical tensor action is natural for those maps.
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

/-- The image of a strongly cocartesian residue pushforward is strongly
cocartesian when the target is cofibered in groupoids. -/
private theorem isStronglyCocartesian_mapResiduePushforward
    {A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    {x : p.Fiber A} {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [IsFibered.InGroupoids q.op] [p.IsStronglyCocartesian (toResidue A) ψ] :
    (BasedCategory.ofFunctor q).p.IsStronglyCocartesian (toResidue A)
      (Φ.map ψ) := sorry

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
      (differentialLinearMapAt Φ x0).rTensor (kerModule f hI) θ := rfl

/-- `tangentTensorMap` acts by `differentialLinearMapAt` on elementary tensors. -/
theorem tangentTensorMap_tmul [IsDeformationCategory p] [IsDeformationCategory q]
    {A' A : ArtinianLocalAlgCat Λ k}
    (Φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x0 : p.Fiber (residue Λ k)) (t : tangentSpaceAt p x0) (i : kerModule f hI) :
    tangentTensorMap Φ f hI x0 (t ⊗ₜ i) = differentialLinearMapAt Φ x0 t ⊗ₜ i :=
  LinearMap.rTensor_tmul (kerModule f hI) (differentialLinearMapAt Φ x0) i t

/-- The canonical tensor action on lift classes at the image residue pushforward. -/
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
    (BasedCategory.ofFunctor q).p A' A (inferInstanceAs (IsDeformationCategory q))
    f hf hI ((Φ.fiberFunctor A).obj x) (objAt Φ x0) (Φ.map ψ)
    (@preserves_isHomLift _ _ _ _ Φ _ _ _ _ (toResidue A) ψ
      (inferInstanceAs (p.IsHomLift (toResidue A) ψ)))
    (by exact isStronglyCocartesian_mapResiduePushforward Φ ψ) θ y

/-- A based morphism of deformation categories intertwines the canonical tensor actions
on lift classes via its differential tensored with the identity on the extension kernel. -/
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
