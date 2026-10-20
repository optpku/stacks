/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.SerreVanishing
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/- Lemma 30.16.2

Let `f : X ⟶ S` be a proper morphism to a Noetherian scheme, `F` a coherent quasicoherent
module on `X`, and `L` a relatively ample invertible module on `X`. Then all positive higher
direct images of `F` twisted by sufficiently large powers of `L` vanish, with one uniform bound.
-/
@[stacks 02O1] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.properRelativelyAmpleCoherentTwist_eventually_isZero :
    (f : X ⟶ S) → [IsNoetherian S] → [IsProper f] →
    (F : X.Modules) → [F.IsQuasicoherent] → [F.IsCoherent] →
    (L : X.Modules) → [L.Invertible] → [RelativelyAmple f L] →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
      IsZero (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom
        (F ⊗ L ^⊗ (n : ℤ)) p))
