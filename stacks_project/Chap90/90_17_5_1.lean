/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.SelfPullbackLifts

open CategoryTheory

universe u v w

/- 90.17.5.1 The comparison isomorphism induces a bijection from lifts over
A' ×_A A' to lifts over A' ×_k k[ker f]. -/
@[stacks 06TA] #check (CategoryTheory.Functor.liftsSelfPullbackIsoEquiv :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type v} [CategoryTheory.Category.{w} F]
    {p : CategoryTheory.Functor F (ArtinianLocalAlgCat Λ k)}
    [CategoryTheory.Functor.IsDeformationCategory p]
    {A' A : ArtinianLocalAlgCat Λ k} (f : A' ⟶ A)
    (hf : Function.Surjective f.hom)
    (hI : IsLocalRing.maximalIdeal A'.carrier * RingHom.ker f.hom.toRingHom = ⊥)
    (x : p.Fiber A),
    CategoryTheory.Functor.lifts p (ArtinianLocalAlgCat.selfPullbackToBase f) x ≃
      CategoryTheory.Functor.lifts p
        (ArtinianLocalAlgCat.squareZeroPullbackToBase A' (ArtinianLocalAlgCat.kerModule f hI) f) x)
