/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

open AlgebraicGeometry

/- Lemma 38.2.8: for an étale morphism, a point is weakly associated to the pullback of a
quasicoherent module if and only if its image is weakly associated to the original module. -/
@[stacks 05FP] #check
  (AlgebraicGeometry.Scheme.Modules.mem_weakAss_pullback_iff_of_etale :
    ∀ {U S : Scheme.{u}} (h : U ⟶ S) [Etale h]
      (𝒢 : S.Modules) [𝒢.IsQuasicoherent] (u : U),
      u ∈ ((Scheme.Modules.pullback h).obj 𝒢).weakAss ↔ h u ∈ 𝒢.weakAss)
