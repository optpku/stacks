/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 33.25.2: let `k` be a perfect field, let `f : X ⟶ Spec(k)` be locally of finite type,
assume `X` is reduced and `Ω[f.toShHom]` is locally free. Then `f` is smooth. -/
@[stacks 04QP] #check
  (AlgebraicGeometry.instSmoothOfPerfectFieldOfIsReducedOfIsLocallyFreeDifferentials :
    ∀ {X : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
      (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [IsReduced X]
      [(Ω[f.toShHom]).IsLocallyFree], Smooth f)
