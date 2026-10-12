/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap38.Lemma_38_20_9
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)

/- Definition 38.20.10: `ℱ` is flat over `S` in dimensions at least `n` when the
equivalent conditions of Lemma 38.20.9 hold. -/
@[stacks 0CWG] #check
  (AlgebraicGeometry.Scheme.Modules.flatOverInDimensionsGE ℱ f n : Prop)
