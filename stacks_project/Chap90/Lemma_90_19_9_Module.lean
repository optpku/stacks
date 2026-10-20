module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Module

/-!
# Linear comparison of infinitesimal automorphisms

The infinitesimal-automorphism module is canonically identified with the
identity tangent space of the automorphism functor.
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

#check (CategoryTheory.Functor.infinitesimalAutomorphismsAtLinearEquiv p x0 x0' φ :
    infinitesimalAutomorphismsAt p x0 x0' φ ≃ₗ[k]
      idTangentSpace p (fiberInclusion.obj x0))
