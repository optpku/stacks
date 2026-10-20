/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap77.Lemma_77_8_5_ClosedImmersion
public import stacks_project.Chap77.Lemma_77_8_5_ZeroFunctor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable [FinitePresentation f] [𝒢.IsFinitePresentation]
variable (u : ℱ ⟶ 𝒢)
variable (hG_flat : ∀ x : Points X, flatOverAt 𝒢 f x)
variable (hG_pure : 𝒢.IsPureOver f)

/- Lemma 77.8.5 (1): In Situation 77.7.1, if `f` is of finite presentation, and
`𝒢` is of finite presentation, flat over `B`, and pure relative to `B`, then
`F_zero` is an algebraic space. -/
@[stacks 0CWC] #check
  (zeroOverSFunctor.isAlgebraicSpace f hG_flat hG_pure u :
    IsAlgebraicSpace (zeroOverSFunctor f u))

section

variable [IsAlgebraicSpace (zeroOverSFunctor f u)]

/- Lemma 77.8.5 (2): In Situation 77.7.1, if `f` is of finite presentation, and
`𝒢` is of finite presentation, flat over `B`, and pure relative to `B`, then
`F_zero ⟶ B` is a closed immersion. -/
@[stacks 0CWC] #check
  (zeroOverSFunctor.isClosedImmersion_toB f hG_flat hG_pure u :
    IsClosedImmersion (zeroOverSFunctor.toB f u))

section

variable [ℱ.IsFiniteType]

/- Lemma 77.8.5 (3): In Situation 77.7.1, if in addition `ℱ` is of finite type,
then `F_zero ⟶ B` is of finite presentation. -/
@[stacks 0CWC] #check
  (zeroOverSFunctor.finitePresentation_toB f hG_flat hG_pure u :
    FinitePresentation (zeroOverSFunctor.toB f u))

end

end
