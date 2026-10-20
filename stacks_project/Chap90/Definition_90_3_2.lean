/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension
import StacksCheckRecall

/-!
# Small extensions

A morphism in the base category is a small extension when it is surjective
and its kernel is a nonzero principal ideal annihilated by the source maximal
ideal.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Definition 90.3.2: a morphism in the base category is small exactly when it is
surjective with a nonzero principal kernel annihilated by the source maximal ideal. -/
@[stacks 06GD] #check (ArtinianLocalAlgCat.isSmallExtension_iff :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    ArtinianLocalAlgCat.IsSmallExtension f ↔
      Function.Surjective f.toRingHom ∧
        (RingHom.ker f.toRingHom).IsPrincipal ∧
        RingHom.ker f.toRingHom ≠ ⊥ ∧
        ArtinianLocalAlgCat.maximalIdeal B * RingHom.ker f.toRingHom = ⊥)
