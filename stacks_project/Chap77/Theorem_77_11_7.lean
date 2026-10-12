/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap77.Theorem_77_11_7_Functor
public import stacks_project.Chap77.Theorem_77_11_7_Space
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
variable [FinitePresentation f] [ℱ.IsFinitePresentation]
variable (n : ℕ) (h_pure : ℱ.IsPureOver f)

/- Theorem 77.11.7 (1): In Situation 77.11.4, if `f` is of finite presentation,
`ℱ` is an `𝒪_X`-module of finite presentation, and `ℱ` is pure relative to `Y`,
then `F_n` is an algebraic space. -/
@[stacks 0CX1] #check
  (Flattening.flatInDimensionsOverSFunctor.isAlgebraicSpace f ℱ n h_pure :
    IsAlgebraicSpace (Flattening.flatInDimensionsOverSFunctor f ℱ n))

section

variable [IsAlgebraicSpace (Flattening.flatInDimensionsOverSFunctor f ℱ n)]

/- Theorem 77.11.7 (2): In Situation 77.11.4, if `f` is of finite presentation,
`ℱ` is an `𝒪_X`-module of finite presentation, and `ℱ` is pure relative to `Y`,
then `F_n ⟶ Y` is a monomorphism. -/
@[stacks 0CX1] #check
  (Flattening.flatInDimensionsOverSFunctor.instMono_toY f ℱ n :
    Mono (Flattening.flatInDimensionsOverSFunctor.toY f ℱ n))

/- Theorem 77.11.7 (3): In Situation 77.11.4, if `f` is of finite presentation,
`ℱ` is an `𝒪_X`-module of finite presentation, and `ℱ` is pure relative to `Y`,
then `F_n ⟶ Y` is of finite presentation. -/
@[stacks 0CX1] #check
  (Flattening.flatInDimensionsOverSFunctor.finitePresentation_toY f ℱ n h_pure :
    FinitePresentation (Flattening.flatInDimensionsOverSFunctor.toY f ℱ n))

end
