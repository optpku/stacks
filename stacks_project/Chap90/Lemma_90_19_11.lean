/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Torsor
import StacksCheckRecall

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

/- Lemma 90.19.11. Relative infinitesimal automorphisms carry a free transitive
  action by the infinitesimal-automorphism tensor space at the residue pushforward. -/
@[stacks 06JY] #check (CategoryTheory.Functor.infAutAddTorsor :
  ∀ (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥) {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ],
    AddTorsor (infAutTensor f hI x0) (infinitesimalAut p f φ))

#check (CategoryTheory.Functor.infAutTensorLinearEquiv :
  ∀ (f : A' ⟶ A)
    (hI : maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ],
    idTangentSpace p (fiberInclusion.obj x') ⊗[k] kerModule f hI ≃ₗ[k]
      infAutTensor f hI x0)

end CategoryTheory.Functor
