/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap86.Lemma_86_9_5_Existence
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory

universe u

/- Lemma 86.9.5: let `S` be a scheme. Let `X ⟶ Y` be a proper, flat morphism of
algebraic spaces which is of finite presentation. There exists a relative dualizing
complex `(ω, τ)`. -/
@[stacks 0E61] #check (RelativeDualizingComplex.nonempty :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f],
      Nonempty (RelativeDualizingComplex f))
