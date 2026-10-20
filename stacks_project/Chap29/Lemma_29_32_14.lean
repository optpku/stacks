/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Differentials
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.32.14: if `f : X ⟶ S` is a monomorphism of schemes, and in particular if it is an
immersion, then the sheaf of relative differentials `Ω[f.toShHom]` is zero. -/
@[stacks 01UY] #check
  (AlgebraicGeometry.isZero_relativeDifferentials_of_mono :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [Mono f],
      CategoryTheory.Limits.IsZero (Ω[f.toShHom]))
