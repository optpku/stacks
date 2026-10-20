module

public import stacks_project.Chap77.Theorem_77_9_1_ClosedImmersion
public import stacks_project.Chap77.Theorem_77_9_1_IsomorphismFunctor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable [FinitePresentation f] [ℱ.IsFinitePresentation]
variable (u : ℱ ⟶ 𝒢) [Epi u]
variable (h_flat : ∀ x : Points X, flatOverAt ℱ f x)
variable (h_pure : ℱ.IsPureOver f)

/- Theorem 77.9.1 (1): In Situation 77.7.1, if `f` is of finite presentation,
`ℱ` is of finite presentation, flat over `B`, and pure relative to `B`, and `u`
is surjective, then `F_iso` is an algebraic space. -/
@[stacks 0CWD] #check
  (isomorphismOverSFunctor.isAlgebraicSpace f h_flat h_pure u :
    IsAlgebraicSpace (isomorphismOverSFunctor f u))

section

variable [IsAlgebraicSpace (isomorphismOverSFunctor f u)]

/- Theorem 77.9.1 (2): In Situation 77.7.1, if `f` is of finite presentation,
`ℱ` is of finite presentation, flat over `B`, and pure relative to `B`, and `u`
is surjective, then `F_iso ⟶ B` is a closed immersion. -/
@[stacks 0CWD] #check
  (isomorphismOverSFunctor.isClosedImmersion_toB f h_flat h_pure u :
    IsClosedImmersion (isomorphismOverSFunctor.toB f u))

section

variable [𝒢.IsFinitePresentation]

/- Theorem 77.9.1 (3): In Situation 77.7.1, if in addition `𝒢` is of finite
presentation, then `F_iso ⟶ B` is of finite presentation. -/
@[stacks 0CWD] #check
  (isomorphismOverSFunctor.finitePresentation_toB f h_flat h_pure u :
    FinitePresentation (isomorphismOverSFunctor.toB f u))

end

end
