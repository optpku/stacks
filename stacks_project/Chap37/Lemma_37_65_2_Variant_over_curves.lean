/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ReducedFiber.Curve
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

/- Lemma 37.65.2 (Variant over curves): for a flat finite-type morphism to a
one-dimensional regular integral Nagata scheme, a finite function-field extension makes the
normalization of the induced base change smooth at every generic point of every fibre. -/
@[stacks 0BRQ] #check (AlgebraicGeometry.Scheme.Hom.exists_normalizedFunctionFieldExtension_smoothInCodimensionZero :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [Scheme.Hom.FiniteType f]
      [Scheme.Nagata S] [IsIntegral S] [Scheme.Regular S],
    topologicalKrullDim S = 1 →
    ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L)
        (_ : FiniteDimensional S.functionField L),
      let q := Scheme.FunctionFieldExtension.map S L
      let T := q.normalization
      let t : T ⟶ S := q.fromNormalization
      let X_T := pullback f t
      let Y := X_T.normalization
      let ν : Y ⟶ X_T := X_T.normalizationTo
      let g : Y ⟶ T := ν ≫ pullback.snd f t
      g.smoothInCodimensionZero)
