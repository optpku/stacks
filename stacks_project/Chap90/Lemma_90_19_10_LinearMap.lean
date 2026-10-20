module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Map

/-!
# Induced k-linear maps on infinitesimal automorphisms

A morphism of categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
induces a map of infinitesimal automorphism groups at a residue-fibre object.
Under (RS) this map is `k`-linear.
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
