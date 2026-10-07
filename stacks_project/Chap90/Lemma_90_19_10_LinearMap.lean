module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import stacks_project.Chap90.Lemma_90_19_9_Module

/-!
# Induced k-linear maps on infinitesimal automorphisms

A morphism of categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
induces a map of infinitesimal automorphism groups at a residue-fibre object.
Under (RS) this map is `k`-linear.
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor BasedCategory
open scoped Bicategory
open Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
variable [HasRimSchlessinger p] [HasRimSchlessinger q]

namespace CategoryTheory.BasedFunctor

/-- The underlying functor of `ofFunctor q` inherits the Rim-Schlessinger condition. -/
instance instHasRimSchlessinger_ofFunctor
    {E : Type v} [Category.{w} E] (r : E ⥤ ArtinianLocalAlgCat Λ k)
    [HasRimSchlessinger r] :
    HasRimSchlessinger (ofFunctor r).p :=
  inferInstanceAs (HasRimSchlessinger r)

/-- The image of a chosen dual-number pushforward under a based functor. -/
def mapPushforward (φ : ofFunctor p ⥤ᵇ ofFunctor q)
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0') :
    fiberInclusion.obj ((φ.fiberFunctor (residue Λ k)).obj x0) ⟶
      fiberInclusion.obj ((φ.fiberFunctor (dualNumber Λ k)).obj x0') :=
  φ.map ψ

/-- The image of a dual-number pushforward is cocartesian. -/
instance mapPushforward_isCocartesian (φ : ofFunctor p ⥤ᵇ ofFunctor q)
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    (ofFunctor q).p.IsCocartesian (residueToDualNumber Λ k) (mapPushforward φ ψ) := sorry

/-- The image of a dual-number pushforward is strongly cocartesian, since the
target is cofibered in groupoids. -/
instance mapPushforward_isStronglyCocartesian (φ : ofFunctor p ⥤ᵇ ofFunctor q)
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    (ofFunctor q).p.IsStronglyCocartesian (residueToDualNumber Λ k) (mapPushforward φ ψ) :=
  isStronglyCocartesian_of_isCocartesian_inGroupoids

/-- The image of a dual-number pushforward still lies over `residueToDualNumber`. -/
instance mapPushforward_isHomLift (φ : ofFunctor p ⥤ᵇ ofFunctor q)
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    (ofFunctor q).p.IsHomLift (residueToDualNumber Λ k) (mapPushforward φ ψ) :=
  IsStronglyCocartesian.toIsHomLift

/-- The map on infinitesimal automorphisms induced by a based functor, as the
restriction of `mapAut` of the dual-number fibre functor. -/
def infAutMap (φ : ofFunctor p ⥤ᵇ ofFunctor q)
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    infinitesimalAutomorphismsAt p x0 x0' ψ →
      infinitesimalAutomorphismsAt (ofFunctor q).p
        ((φ.fiberFunctor (residue Λ k)).obj x0)
        ((φ.fiberFunctor (dualNumber Λ k)).obj x0') (mapPushforward φ ψ) :=
  fun α ↦ ⟨mapAut x0' (φ.fiberFunctor (dualNumber Λ k)) α.val, sorry⟩

/-- The underlying automorphism of `infAutMap` is `mapAut` of the dual-number
fibre functor. -/
theorem infAutMap_apply (φ : ofFunctor p ⥤ᵇ ofFunctor q)
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (α : infinitesimalAutomorphismsAt p x0 x0' ψ) :
    (infAutMap φ ψ α).val = mapAut x0' (φ.fiberFunctor (dualNumber Λ k)) α.val := sorry

/-- Under (RS), the infinitesimal-automorphism map of a based functor is `k`-linear. -/
theorem isLinearMap_infAutMap (φ : ofFunctor p ⥤ᵇ ofFunctor q)
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    IsLinearMap k (infAutMap φ ψ) := sorry

/-- The `k`-linear map on infinitesimal automorphisms induced by a morphism of
categories cofibered in groupoids satisfying (RS). -/
def infAutLinearMap (φ : ofFunctor p ⥤ᵇ ofFunctor q)
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    infinitesimalAutomorphismsAt p x0 x0' ψ →ₗ[k]
      infinitesimalAutomorphismsAt (ofFunctor q).p
        ((φ.fiberFunctor (residue Λ k)).obj x0)
        ((φ.fiberFunctor (dualNumber Λ k)).obj x0') (mapPushforward φ ψ) :=
  IsLinearMap.mk' (infAutMap φ ψ) (isLinearMap_infAutMap φ ψ)

/-- The underlying function of `infAutLinearMap` is `infAutMap`. -/
theorem infAutLinearMap_apply (φ : ofFunctor p ⥤ᵇ ofFunctor q)
    {x0 : p.Fiber (residue Λ k)} {x0' : p.Fiber (dualNumber Λ k)}
    (ψ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (α : infinitesimalAutomorphismsAt p x0 x0' ψ) :
    infAutLinearMap φ ψ α = infAutMap φ ψ α := sorry

end CategoryTheory.BasedFunctor
