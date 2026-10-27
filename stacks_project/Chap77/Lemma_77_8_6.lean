/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.ZeroFunctor.ProperSupport
import StacksCheckRecall

/-!
# Vanishing functor under proper support

In Situation 77.7.1, if `f` is locally of finite presentation, `𝒢` is of finite
presentation and flat over `B`, and the support of `𝒢` is proper over `B`, then
`F_zero` is an algebraic space and `F_zero ⟶ B` is a closed immersion. If `ℱ` is
of finite type, that morphism is of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

variable [LocallyOfFinitePresentation f] [𝒢.IsFinitePresentation]
variable [Proper ((schemeTheoreticSupport 𝒢).ι ≫ f)]
variable (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x) (u : ℱ ⟶ 𝒢)

/- Lemma 77.8.6 (1): In Situation 77.7.1, if `f` is locally of finite presentation,
`𝒢` is of finite presentation and flat over `B`, and the support of `𝒢` is proper
over `B`, then the functor `F_zero` is an algebraic space. -/
@[stacks 083M] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.zeroOverSFunctor.isAlgebraicSpace_of_properSupport
    f hG_flat u : IsAlgebraicSpace (zeroOverSFunctor f u))

section

variable [IsAlgebraicSpace (zeroOverSFunctor f u)]

/- Lemma 77.8.6 (2): In Situation 77.7.1, if `f` is locally of finite presentation,
`𝒢` is of finite presentation and flat over `B`, and the support of `𝒢` is proper
over `B`, then `F_zero ⟶ B` is a closed immersion. -/
@[stacks 083M] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.zeroOverSFunctor.isClosedImmersion_toB_of_properSupport
    f hG_flat u : IsClosedImmersion (zeroOverSFunctor.toB f u))

section

variable [ℱ.IsFiniteType]

/- Lemma 77.8.6 (3): In Situation 77.7.1, if in addition `ℱ` is of finite type, then
`F_zero ⟶ B` is of finite presentation. -/
@[stacks 083M] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.zeroOverSFunctor.finitePresentation_toB_of_properSupport
    f hG_flat u : FinitePresentation (zeroOverSFunctor.toB f u))

end

end

end AlgebraicGeometry.AlgebraicSpace.Modules
