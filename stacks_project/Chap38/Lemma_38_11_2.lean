/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.DenseOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 38.11.2: a flat morphism locally of finite type is locally of finite presentation
if its restriction to a retrocompact scheme-theoretically dense open is locally of finite
presentation. -/
@[stacks 081P] #check
  (AlgebraicGeometry.LocallyOfFinitePresentation.of_restrict_of_flat :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      [AlgebraicGeometry.LocallyOfFiniteType f] →
      [AlgebraicGeometry.Flat f] →
      (U : S.Opens) →
      IsRetrocompact (U : Set S) →
      AlgebraicGeometry.schemeTheoreticallyDense U →
      [AlgebraicGeometry.LocallyOfFinitePresentation (f ∣_ U)] →
      AlgebraicGeometry.LocallyOfFinitePresentation f)
