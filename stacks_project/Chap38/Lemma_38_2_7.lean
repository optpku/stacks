/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 38.2.7: for a finite flat morphism, a point is weakly associated to the pullback of a
quasicoherent module if and only if its image is weakly associated to the original module. -/
@[stacks 05FN] #check
  (AlgebraicGeometry.Scheme.Modules.mem_weakAss_pullback_iff_of_isFinite_of_flat :
    ∀ {T S : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ S) [AlgebraicGeometry.IsFinite g]
      [AlgebraicGeometry.Flat g] (𝒢 : S.Modules) [𝒢.IsQuasicoherent] (t : T),
      t ∈ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj 𝒢).weakAss ↔
        g t ∈ 𝒢.weakAss)
