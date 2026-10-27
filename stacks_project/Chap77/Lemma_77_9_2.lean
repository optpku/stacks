/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IsomorphismLocus.ProperSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable [LocallyOfFinitePresentation f] [ℱ.IsFinitePresentation]
variable [Proper ((schemeTheoreticSupport ℱ).ι ≫ f)]
variable (h_flat : ∀ x : Points X, flatOverAt ℱ f x) (u : ℱ ⟶ 𝒢) [Epi u]

/- Lemma 77.9.2: In Situation 77.7.1, if `f` is locally of finite presentation,
`ℱ` is locally of finite presentation and flat over `B`, its support is proper over
`B`, and `u` is surjective, then the isomorphism functor is an algebraic space. -/
@[stacks 083N] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismOverSFunctor.isAlgebraicSpace_of_properSupport f h_flat u :
    IsAlgebraicSpace (isomorphismOverSFunctor f u))

section

variable [IsAlgebraicSpace (isomorphismOverSFunctor f u)]

/- Under the same hypotheses, the canonical structural morphism is a closed immersion. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismOverSFunctor.isClosedImmersion_toB_of_properSupport f h_flat u :
    IsClosedImmersion (isomorphismOverSFunctor.toB f u))

variable [𝒢.IsFinitePresentation]

/- If `𝒢` is of finite presentation, the structural morphism is of finite presentation. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismOverSFunctor.finitePresentation_toB_of_properSupport f h_flat u :
    FinitePresentation (isomorphismOverSFunctor.toB f u))

end
