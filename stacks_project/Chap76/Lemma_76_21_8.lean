/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_21_8_NaiveCotangent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.21.8: a morphism of algebraic spaces over a scheme `S` is smooth
exactly when it is locally of finite presentation, its degree `-1`
naive-cotangent homology vanishes, and its relative differentials are finite
locally free. Degree-zero homology of `NL[f]` is identified with `Ω[f]` by
`homologyZeroIso`. -/
@[stacks 0D12]
#check (AlgebraicGeometry.AlgebraicSpace.Smooth.iff_naiveCotangent :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Smooth f ↔ LocallyOfFinitePresentation f ∧
      IsZero ((NL[f]).homology (-1)) ∧ (Ω[f]).IsFiniteLocallyFree)
