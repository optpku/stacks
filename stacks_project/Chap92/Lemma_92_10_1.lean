/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.PolynomialResolution.Frobenius
import StacksCheckRecall

/-!
# Homotopy of Frobenius maps on the standard resolution

The map induced by the Frobenius square is simplicially homotopic to degreewise Frobenius.
-/

open CategoryTheory
open CategoryTheory.CommRingCat.Under.PolynomialResolution.Frobenius

universe u

/- Lemma 92.10.1. For a prime `p` vanishing in `A`, standard-resolution functoriality
induced by the Frobenius square is homotopic to Frobenius on each resolution term. -/
@[stacks 0G5Y] #check
  (CategoryTheory.CommRingCat.Under.PolynomialResolution.Frobenius.functoriality_homotopic_degreewise :
    (p : ℕ) → [Fact p.Prime] → {A : CommRingCat.{u}} → (hp : (p : A) = 0) →
      (B : Under A) → SimplicialObject.Homotopic (functoriality p hp B) (degreewise p hp B))
