/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints.Density
import StacksCheckRecall

universe u

@[expose] public section

/-!
# A reduced scheme with a schematically dense open missing a weakly associated point
-/

/- Lemma 110.63.1 -/
@[stacks 084K] #check (AlgebraicGeometry.Scheme.exists_isReduced_denseOpen_missing_weakAss :
  ∃ (X : AlgebraicGeometry.Scheme.{u}) (_ : AlgebraicGeometry.IsReduced X)
    (U : X.Opens) (x : X),
    AlgebraicGeometry.schemeTheoreticallyDense U ∧ x ∈ X.weakAss ∧ x ∉ U)
