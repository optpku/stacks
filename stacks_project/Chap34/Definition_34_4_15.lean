/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

variable (S : Scheme.{u})

/- Definition 34.4.15: the inverse image for identity-base small-to-big étale
relocalization is the restriction functor from sheaves on the big étale site of `S` to sheaves
on the small étale site of `S`; its value on `𝓕` is denoted `𝓕|_{S_ét}`. -/
@[stacks 04BT] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.inverseImage (𝟙 S) :
    Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)) ⥤
      Sheaf S.smallEtaleTopology (Type (u + 1)))
