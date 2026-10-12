/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap90.Definition_90_19_1
public import stacks_project.Chap90.Definition_90_19_2
public import stacks_project.Chap90.Lemma_90_10_7_DualNumber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing of infinitesimal automorphisms

If `p` is cofibered in groupoids and satisfies (RS), a morphism `φ : x' ⟶ x` lies
over a surjection, and `x0` is a residue-fibre pushforward of `x`, then
`Inf_{x0}(F) = 0` implies `Inf(x'/x) = 0`.
-/

@[expose] public section

open CategoryTheory
open Functor Fiber ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} [HasRimSchlessinger p]
variable {A' A : ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- The Rim-Schlessinger condition includes being cofibered in groupoids. -/
instance instIsFiberedInGroupoids_ofHasRimSchlessinger
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] :
    IsFibered.InGroupoids p.op :=
  HasRimSchlessinger.isCofiberedInGroupoids

/-- Lemma 90.19.12. Let `p : F ⥤ ArtinianLocalAlgCat Λ k` be cofibered in groupoids
over `C_Λ` and satisfy (RS). Let `φ : x' ⟶ x` be a morphism in `F` lying over a
surjective ring map `f : A' ⟶ A`, and let `x0` be a pushforward of `x` to `F(k)`.
If `Inf_{x0}(F) = 0`, then `Inf(x'/x) = 0`. -/
@[stacks 06JZ]
theorem infinitesimalAut_eq_bot (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    {x0' : p.Fiber (dualNumber Λ k)}
    (χ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) χ]
    (h : infinitesimalAutomorphismsAt p x0 x0' χ = ⊥) :
    infinitesimalAut p f φ = ⊥ := sorry

/-- Under the hypotheses of `infinitesimalAut_eq_bot`, every infinitesimal automorphism
of `x'` over `x` is the identity. -/
theorem eq_one_of_mem_infinitesimalAut (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    {x' : p.Fiber A'} {x : p.Fiber A}
    (φ : fiberInclusion.obj x' ⟶ fiberInclusion.obj x) [p.IsHomLift f φ]
    {x0 : p.Fiber (residue Λ k)}
    (ψ : fiberInclusion.obj x ⟶ fiberInclusion.obj x0)
    [p.IsHomLift (toResidue A) ψ] [p.IsStronglyCocartesian (toResidue A) ψ]
    {x0' : p.Fiber (dualNumber Λ k)}
    (χ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) χ]
    (h : infinitesimalAutomorphismsAt p x0 x0' χ = ⊥)
    {α : Aut x'} (hα : α ∈ infinitesimalAut p f φ) : α = 1 := sorry

end CategoryTheory.Functor
