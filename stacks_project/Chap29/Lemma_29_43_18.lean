/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.NonvanishingOpen
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.43.18: if `f : X ⟶ S` is universally closed and `L` is relatively ample over
`f`, then the nonvanishing open of every global section of `L` is affine over `S`. -/
@[stacks 0EKE] #check
  (AlgebraicGeometry.RelativelyAmple.isAffineHom_sectionNonvanishingOpen :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
      [h : RelativelyAmple f L] [UniversallyClosed f]
      (s : Γ(L, ⊤)),
      IsAffineHom ((h.invertible.sectionNonvanishingOpen s).ι ≫ f))
