/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Pushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 31.5.9: for a quasi-compact and quasi-separated morphism `f : X ⟶ S` and a
quasi-coherent module `ℱ` on `X`, a point outside `Set.range f.base` is not weakly associated
to the pushforward of `ℱ`. -/
@[stacks 0AVN] #check
  (AlgebraicGeometry.Scheme.Modules.not_mem_weakAss_pushforward_of_not_mem_range :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (s : S),
      s ∉ Set.range f.base →
        s ∉ ((Scheme.Modules.pushforward f).obj ℱ).weakAss)
