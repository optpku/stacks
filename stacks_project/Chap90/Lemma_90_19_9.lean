/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Module
import StacksCheckRecall

/-!
# Lemma 90.19.9

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and satisfies
(RS), and `x0` is a residue-fibre object, then `Inf_{x0}(F)` equals
`T_id Aut(x0)` as sets, and therefore carries the natural `k`-vector space
structure of Lemma 90.19.7 in which addition agrees with composition of
automorphisms.
-/

@[expose] public section

open CategoryTheory hiding Linear
open CategoryTheory.Functor
open ArtinianLocalAlgCat
open Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
variable (x0 : p.Fiber (residue Λ k))
variable (x0' : p.Fiber (dualNumber Λ k))
variable (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
variable [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]

/- Lemma 90.19.9: Infinitesimal automorphisms equal the identity tangent space
of the automorphism functor, with its natural k-vector space structure and
addition given by composition of automorphisms. -/
@[stacks 06JX] #check (CategoryTheory.Functor.infinitesimalAutomorphismsAtLinearEquiv p x0 x0' φ :
    infinitesimalAutomorphismsAt p x0 x0' φ ≃ₗ[k]
      idTangentSpace p (fiberInclusion.obj x0))

#check (CategoryTheory.Functor.infinitesimalAutomorphismsAt_eq_idTangentSpace p x0 :
    infinitesimalAutomorphismsAt p x0
        (idTangentSpaceObj p (fiberInclusion.obj x0)) (infAutIdTangentHom p x0) =
      idTangentSpace p (fiberInclusion.obj x0))

#check (CategoryTheory.Functor.instModule_infinitesimalAutomorphismsAt p x0 x0' φ :
    Module k (infinitesimalAutomorphismsAt p x0 x0' φ))

#check (CategoryTheory.Functor.infinitesimalAutomorphismsAt_add_eq_mul p x0 x0' φ :
    ∀ α β : infinitesimalAutomorphismsAt p x0 x0' φ, α + β = α * β)
