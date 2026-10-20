/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor.Limit
import StacksCheckRecall

/-!
# Lemma 99.3.6

In Situation 99.3.1, if `F` is of finite presentation and `f` is quasi-compact
and quasi-separated, then `Hom(F, G)` is limit preserving.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

/- Lemma 99.3.6: In Situation 99.3.1, finite presentation of `F` and
quasi-compactness and quasi-separatedness of `f` imply that `Hom(F, G)` is
limit preserving. -/
@[stacks 08K4] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor_preservesDirectedAffineLimits :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
      [QuasiCompact f] [QuasiSeparated f] (F G : X.Modules)
      [F.IsQuasicoherent] [G.IsQuasicoherent] [F.IsFinitePresentation],
      SchemeOver.PreservesDirectedAffineLimits B (Modules.homFunctor f F G))
