module

public import stacks_project.Chap90.Lemma_90_19_11_Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Free transitive action on infinitesimal automorphisms

If `p` is cofibered in groupoids and satisfies (RS), and `φ : x' ⟶ x` lies over a
surjection `f : A' ⟶ A` whose kernel `I` is annihilated by `m_{A'}`, then
`Inf(x'/x)` is a torsor under `Inf_{x0}(F) ⊗[k] I`, identified with
`T_id Aut(x') ⊗[k] I`.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open Functor Fiber ArtinianLocalAlgCat IsLocalRing
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} [HasRimSchlessinger p]
variable {A' A : ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- Lemma 90.19.11 (1) Let F be a category cofibered in groupoids over C_Λ
satisfying (RS). Let x' ⟶ x be a morphism lying over a surjective ring map
A' ⟶ A with kernel I annihilated by m_{A'}. Let x0 be a pushforward of x to
F(k). Then Inf(x'/x) has a free and transitive action by
Inf_{x0}(F) ⊗[k] I. The action is constructed from the Aut-fibre composite Φ of
90.17.5.1–3; Inf is a group, so no extra nonempty hypothesis is needed. -/
@[stacks 06JY]
abbrev infAutAddTorsor (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    AddTorsor (infAutTensor f hI x0) (infinitesimalAut p f φ) :=
  instAddTorsor_infAut f hI hf φ ψ

/-- The tensor action of `θ` sends `α` to `α'` if and only if the transported
difference recovers `θ`. -/
theorem infAutAddTorsor_spec (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : infAutTensor f hI x0)
    (α α' : infinitesimalAut p f φ) :
    infAutVAdd f hI hf φ ψ θ α = α' ↔ infAutVSub f hI hf φ ψ α' α = θ := sorry

/-- Lemma 90.19.11 (2) The acting groups are identified as
T_id Aut(x') ⊗[k] I ≃ₗ[k] Inf_{x0}(F) ⊗[k] I, via the identity-tangent comparison
of Lemma 90.19.7 and the infinitesimal-automorphism comparison of Lemma 90.19.9,
together with the unique cocartesian comparison of the selected residue
pushforward of x' with the given x0. -/
@[stacks 06JY]
def infAutTensorLinearEquiv (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ] :
    idTangentSpace p (fiberInclusion.obj x') ⊗[k] kerModule f hI ≃ₗ[k]
      infAutTensor f hI x0 :=
  TensorProduct.congr (infAutIdTangentInfLinearEquiv f φ ψ)
    (LinearEquiv.refl k (kerModule f hI))

/-- `infAutTensorLinearEquiv` is `TensorProduct.congr` of
`infAutIdTangentInfLinearEquiv` with the identity on `kerModule`. -/
theorem infAutTensorLinearEquiv_apply (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    (θ : idTangentSpace p (fiberInclusion.obj x') ⊗[k] kerModule f hI) :
    infAutTensorLinearEquiv f hI φ ψ θ =
      TensorProduct.congr (infAutIdTangentInfLinearEquiv f φ ψ)
        (LinearEquiv.refl k (kerModule f hI)) θ := sorry

end CategoryTheory.Functor
