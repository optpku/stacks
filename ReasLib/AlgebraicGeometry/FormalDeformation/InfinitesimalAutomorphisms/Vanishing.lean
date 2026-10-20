module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms

/-!
# Vanishing of infinitesimal automorphisms

For a category satisfying the Rim-Schlessinger condition, vanishing of infinitesimal
automorphisms at a residue pushforward implies vanishing of relative infinitesimal
automorphisms over every surjection.
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

/-- In a category cofibered in groupoids satisfying the Rim-Schlessinger condition,
the relative infinitesimal automorphisms of a morphism over a surjection vanish if the
infinitesimal automorphisms at a residue pushforward of its target vanish. -/
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

end CategoryTheory.Functor
