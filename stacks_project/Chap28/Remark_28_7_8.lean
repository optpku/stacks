/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Connected
import StacksCheckRecall

universe u

/- Remark 28.7.8 (1): if a normal scheme `X` is locally Noetherian, then `X` is integral if
and only if `X` is connected. -/
@[stacks 033O] #check
  (AlgebraicGeometry.IsLocallyNoetherian.isIntegral_iff_connectedSpace_of_isNormal :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      X.isNormal → (AlgebraicGeometry.IsIntegral X ↔ ConnectedSpace X))

/- Remark 28.7.8 (2): there exists a connected affine normal scheme whose local rings
`O_{X, x}` are domains for all points `x`, but whose underlying topological space is not
irreducible. -/
@[stacks 033O] #check
  (AlgebraicGeometry.Scheme.exists_isAffine_isNormal_connectedSpace_not_irreducibleSpace :
    ∃ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.IsAffine X ∧ X.isNormal ∧ ConnectedSpace X ∧
        (∀ x : X, IsDomain (X.presheaf.stalk x)) ∧ ¬ IrreducibleSpace X)
