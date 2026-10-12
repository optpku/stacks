/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions
import StacksCheckRecall

open CategoryTheory

noncomputable section

universe u

open AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (n : ℕ)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/- 38.20.11.1: the subterminal functor `F_n` assigns to `T ⟶ S` a singleton exactly when the
base change of `ℱ` is flat over `T` in dimensions at least `n`, and the empty type otherwise. -/
@[stacks 05MU] #check
  (AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor f ℱ n : (Over S)ᵒᵖ ⥤ Type u)
