/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.VanishingSections
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.47.1: for a proper scheme over a field, sections of sufficiently high tensor powers
of an ample invertible module that vanish on a closed subscheme generate on its complement, and
the resulting canonical morphism to their projective scheme is an immersion. -/
@[stacks 0FD5] #check
  (AlgebraicGeometry.Scheme.Modules.IsAmple.eventualVanishingSectionsGenerateAndInduceImmersion :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (L : X.Modules) [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L]
      (Z : X.IdealSheafData),
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        Scheme.Modules.VanishingSections.GeneratesAndInducesImmersion f Z L n)
