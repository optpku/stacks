/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.UniversalProperty
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 31.32.7: Let `X` be a scheme. Let `Z ⊆ X` be an effective Cartier divisor. The blowup
of `X` in `Z` is the identity morphism of `X`. -/
@[stacks 0807] #check
  (AlgebraicGeometry.instIsBlowupIdentity :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) (I : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor I.subschemeι],
      AlgebraicGeometry.IsBlowup (𝟙 X) I)
