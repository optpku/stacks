/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Setoids
import StacksCheckRecall

/-!
# Vanishing of infinitesimal automorphisms and the iso-class morphism

If `p` is cofibered in groupoids and satisfies (RS), then `Inf_{x0}(F) = ⊥` if and
only if the canonical morphism `toIsoClass (sliceAt p x0)` is an equivalence of
categories cofibered in groupoids.
-/

@[expose] public section

open CategoryTheory
open Functor Fiber ArtinianLocalAlgCat
open scoped BasedFunctor

universe u v w

/- Lemma 90.19.13. Let `p : F ⥤ ArtinianLocalAlgCat Λ k` be a category cofibered
in groupoids over `ArtinianLocalAlgCat Λ k` satisfying (RS), and let `x0` be an
object of the residue fibre `p.Fiber (residue Λ k)`. Then
`infinitesimalAutomorphismsAt p x0 x0' φ = ⊥` if and only if the canonical
morphism `BasedFunctor.toIsoClass (sliceAt p x0)` of categories cofibered in
groupoids is an equivalence. -/
@[stacks 06K0] #check (CategoryTheory.Functor.infinitesimalAutomorphismsAt_eq_bot_iff :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [Category.{w} F]
    {p : F ⥤ ArtinianLocalAlgCat Λ k} [HasRimSchlessinger p]
    (x0 : p.Fiber (residue Λ k)) {x0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ],
    infinitesimalAutomorphismsAt p x0 x0' φ = ⊥ ↔
      BasedFunctor.IsEquivalence (BasedFunctor.toIsoClass (sliceAt p x0)))
