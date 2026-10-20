/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.Order.Bounds.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Quotient
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger

/-!
# Ideals admitting lifts of objects over Artinian local algebras

The infimum of the ideals admitting a lift is the least such ideal under
Schlessinger's condition (S1) for a surjection with maximally annihilated kernel.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat IsLocalRing

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Ideals inside the kernel through whose quotients a fixed object admits a lift. -/
def liftIdeals (p : F ⥤ ArtinianLocalAlgCat Λ k) {B A : ArtinianLocalAlgCat Λ k}
    (f : B ⟶ A) {x : F} (hx : p.obj x = A) : Set (Ideal B.carrier) :=
  {J | ∃ (hJ : J ≤ RingHom.ker f.hom.toRingHom) (y : F) (φ : y ⟶ x),
      p.IsHomLift (quotientFactor f J hJ) φ}

/-- A morphism over the quotient factor exhibits membership among the lift ideals. -/
theorem mem_liftIdeals (p : F ⥤ ArtinianLocalAlgCat Λ k)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) {x : F} (hx : p.obj x = A)
    {J : Ideal B.carrier} (hJ : J ≤ RingHom.ker f.hom.toRingHom)
    {y : F} {φ : y ⟶ x} (hφ : p.IsHomLift (quotientFactor f J hJ) φ) :
    J ∈ p.liftIdeals f hx := sorry

/-- A lift ideal is precisely an ideal in the kernel admitting a morphism over its quotient factor. -/
theorem mem_liftIdeals_iff (p : F ⥤ ArtinianLocalAlgCat Λ k)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) {x : F} (hx : p.obj x = A)
    {J : Ideal B.carrier} :
    J ∈ p.liftIdeals f hx ↔
      ∃ (hJ : J ≤ RingHom.ker f.hom.toRingHom) (y : F) (φ : y ⟶ x),
        p.IsHomLift (quotientFactor f J hJ) φ := sorry

/-- The infimum of all ideals through whose quotients the fixed object admits a lift. -/
noncomputable def smallestLiftIdeal (p : F ⥤ ArtinianLocalAlgCat Λ k)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) {x : F} (hx : p.obj x = A) :
    Ideal B.carrier :=
  sInf (p.liftIdeals f hx)

/-- The smallest-lift-ideal construction is the infimum of the lift ideals. -/
theorem smallestLiftIdeal_eq_sInf (p : F ⥤ ArtinianLocalAlgCat Λ k)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) {x : F} (hx : p.obj x = A) :
    p.smallestLiftIdeal f hx = sInf (p.liftIdeals f hx) := sorry

/-- For a cofibered category in groupoids satisfying (S1), the lift ideals along a
surjection with kernel annihilated by the source maximal ideal have a least element. -/
theorem smallestLiftIdeal_isLeast (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom)
    (hI : maximalIdeal B.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    {x : F} (hx : p.obj x = A) :
    IsLeast (p.liftIdeals f hx) (p.smallestLiftIdeal f hx) := sorry

end CategoryTheory.Functor
