/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty.Regular
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 36.36.8: a quasi-compact regular scheme with affine diagonal has the resolution
property. -/
@[stacks 0F8A]
#check (AlgebraicGeometry.Scheme.hasResolutionProperty_of_compact_regular_affineDiagonal :
  ∀ {X : Scheme.{u}} [CompactSpace X] [AlgebraicGeometry.Scheme.Regular X]
    [AlgebraicGeometry.IsAffineHom (prod.lift (𝟙 X) (𝟙 X))],
      AlgebraicGeometry.Scheme.HasResolutionProperty X)
