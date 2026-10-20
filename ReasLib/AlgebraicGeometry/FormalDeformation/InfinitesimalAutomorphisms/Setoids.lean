/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.ToIsoClass.Equivalence
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Vanishing
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Infinitesimal vanishing and setoid residue slices
-/

@[expose] public section

open CategoryTheory
open Functor Fiber ArtinianLocalAlgCat
open scoped BasedFunctor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- The infinitesimal automorphism group of a residue-fibre object vanishes if and
only if the opposite of the residue slice `sliceAt p x0` is fibered in setoids. -/
theorem infinitesimalAutomorphismsAt_eq_bot_iff_inSetoids [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphismsAt p x0 x0' φ = ⊥ ↔
      IsFibered.InSetoids (sliceAt p x0).op := sorry

/-- In a category cofibered in groupoids satisfying the Rim-Schlessinger condition,
infinitesimal automorphisms at a residue-fibre object vanish if and only if the canonical
morphism from its residue slice to fibrewise isomorphism classes is an equivalence. -/
@[stacks 06K0]
theorem infinitesimalAutomorphismsAt_eq_bot_iff [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphismsAt p x0 x0' φ = ⊥ ↔
      BasedFunctor.IsEquivalence (BasedFunctor.toIsoClass (sliceAt p x0)) :=
  (infinitesimalAutomorphismsAt_eq_bot_iff_inSetoids (p := p) x0 φ).trans
    (BasedFunctor.toIsoClass_isEquivalence_iff_inSetoids (sliceAt p x0)).symm

end CategoryTheory.Functor
