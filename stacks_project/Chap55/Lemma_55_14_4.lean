/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal.Contraction

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 55.14.4 -/
@[stacks 0CDF] #check (AlgebraicGeometry.atWorstNodal_of_exceptionalCurveContraction :
    ∀ (R K k : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K] [Field k],
      (k ≃+* IsLocalRing.ResidueField R) →
      ∀ {X X' : Scheme.{u}} [IsNoetherian X],
        (E : X.IdealSheafData) → [IsExceptionalCurveFirstKind E] →
        (x : closedPoints X') → (b : X ⟶ X') → IsContraction E b x →
        (f : X' ⟶ Spec (.of R)) → [AtWorstNodal (b ≫ f)] → AtWorstNodal f)
