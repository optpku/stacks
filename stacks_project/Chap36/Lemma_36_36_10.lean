/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty.AffineDiagonal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 36.36.10: a quasi-compact, quasi-separated scheme with the resolution property has
affine diagonal. -/
@[stacks 0F8C] #check
  (AlgebraicGeometry.Scheme.affineDiagonal_of_hasResolutionProperty :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X],
      AlgebraicGeometry.Scheme.HasResolutionProperty X →
        IsAffineHom (prod.lift (𝟙 X) (𝟙 X)))
