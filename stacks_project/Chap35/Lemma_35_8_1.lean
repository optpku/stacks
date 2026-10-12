/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.PullbackSections.Sheaf
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 35.8.1 (1): for the Zariski, étale, smooth, syntomic, and fppf topologies,
pullback sections of a quasi-coherent module satisfy the sheaf condition. -/
@[stacks 03DT] #check
  (AlgebraicGeometry.Scheme.Modules.PullbackSections.isSheaf_standard :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) (ℱ : S.Modules) [ℱ.IsQuasicoherent],
      Presheaf.IsSheaf (τ.overTopology S)
        (AlgebraicGeometry.Scheme.Modules.PullbackSections.over S ℱ))

/- Lemma 35.8.1 (2): pullback sections of a quasi-coherent module satisfy the sheaf
condition for the fpqc topology. -/
@[stacks 03DT] #check
  (AlgebraicGeometry.Scheme.Modules.PullbackSections.isSheaf_fpqc :
    ∀ (S : Scheme.{u}) (ℱ : S.Modules) [ℱ.IsQuasicoherent],
      Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
        (AlgebraicGeometry.Scheme.Modules.PullbackSections.over S ℱ))
