/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Map
import StacksCheckRecall

/-!
# Lemma 90.19.10

A morphism `φ : ℱ ⟶ 𝒢` of categories cofibered in groupoids over `C_Λ`
satisfying (RS) induces a `k`-linear map `Inf_x0(ℱ) ⟶ Inf_φ(x0)(𝒢)` at any
residue-fibre object `x0`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor BasedCategory
open scoped Bicategory
open Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
variable [HasRimSchlessinger p] [HasRimSchlessinger q]

/- Lemma 90.19.10: Let φ : ℱ ⟶ 𝒢 be a morphism of categories cofibered in
groupoids over C_Λ satisfying (RS). Let x0 ∈ Ob(ℱ(k)). Then φ induces a
k-linear map Inf_x0(ℱ) ⟶ Inf_φ(x0)(𝒢). -/
@[stacks 07W6]
#check (CategoryTheory.BasedFunctor.infAutLinearMap :
  ∀ (φ : ofFunctor p ⥤ᵇ ofFunctor q)
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ],
    infinitesimalAutomorphismsAt p x0 x0' ψ →ₗ[k]
      infinitesimalAutomorphismsAt (ofFunctor q).p
        ((φ.fiberFunctor (residue Λ k)).obj x0)
        ((φ.fiberFunctor (dualNumber Λ k)).obj x0')
        (CategoryTheory.BasedFunctor.mapPushforward φ ψ))
