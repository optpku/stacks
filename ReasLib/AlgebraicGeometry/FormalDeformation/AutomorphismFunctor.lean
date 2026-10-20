/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger
public import ReasLib.CategoryTheory.Fibered.AutomorphismFunctor

/-!
# Pullback preservation by automorphism functors

The automorphism functor of an object in a category cofibered in groupoids
satisfying the Rim-Schlessinger condition preserves pullback squares along
surjective algebra maps.
-/

@[expose] public section

attribute [instance] CategoryTheory.Functor.HasRimSchlessinger.isCofiberedInGroupoids

open CategoryTheory Limits Under

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- For a category cofibered in groupoids satisfying the Rim-Schlessinger condition,
the automorphism functor of any object sends pullback squares in the under-category
whose second underlying algebra map is surjective to pullback squares of types. -/
theorem HasRimSchlessinger.autFunctor_isPullback
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] (x : F)
    {W W1 W2 P : Under (p.obj x)}
    (f1 : W1 ⟶ W) (f2 : W2 ⟶ W) (π1 : P ⟶ W1) (π2 : P ⟶ W2)
    (hf2 : Function.Surjective f2.right.hom) (h : IsPullback π1 π2 f1 f2) :
    IsPullback ((autFunctor p x).map π1) ((autFunctor p x).map π2)
      ((autFunctor p x).map f1) ((autFunctor p x).map f2) := sorry

/-- A pullback square in the under-category induces the map from automorphisms
over its vertex to the compatible pair of their images under its projections. -/
noncomputable def autFunctorComparison
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] (x : F)
    {W W1 W2 P : Under (p.obj x)}
    (f1 : W1 ⟶ W) (f2 : W2 ⟶ W) (π1 : P ⟶ W1) (π2 : P ⟶ W2)
    (h : IsPullback π1 π2 f1 f2) :
    (autFunctor p x).obj P →
      Types.PullbackObj ((autFunctor p x).map f1) ((autFunctor p x).map f2) :=
  (PullbackCone.mk ((autFunctor p x).map π1) ((autFunctor p x).map π2)
    ((autFunctor p x).map_commSq h.toCommSq).w).toPullbackObj

/-- The automorphism comparison map has as its underlying pair the images under
the two projections of the pullback square. -/
theorem autFunctorComparison_spec
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] (x : F)
    {W W1 W2 P : Under (p.obj x)}
    (f1 : W1 ⟶ W) (f2 : W2 ⟶ W) (π1 : P ⟶ W1) (π2 : P ⟶ W2)
    (h : IsPullback π1 π2 f1 f2) (α : (autFunctor p x).obj P) :
    (autFunctorComparison p x f1 f2 π1 π2 h α).1 =
      ((autFunctor p x).map π1 α, (autFunctor p x).map π2 α) := sorry

/-- For a category satisfying the Rim-Schlessinger condition, the automorphism
comparison map is bijective on pullback squares whose second underlying algebra
map is surjective. -/
theorem HasRimSchlessinger.autFunctorComparison_bijective
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] (x : F)
    {W W1 W2 P : Under (p.obj x)}
    (f1 : W1 ⟶ W) (f2 : W2 ⟶ W) (π1 : P ⟶ W1) (π2 : P ⟶ W2)
    (h : IsPullback π1 π2 f1 f2) (hf2 : Function.Surjective f2.right.hom) :
    Function.Bijective (autFunctorComparison p x f1 f2 π1 π2 h) := sorry

end CategoryTheory.Functor
