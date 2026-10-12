/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Small
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

universe u

variable (S : Scheme.{u})

/- Definition 34.3.15: the inverse image for identity-base small-to-big Zariski
relocalization is the restriction functor from sheaves on the big Zariski site of `S` to sheaves
on the small Zariski site of `S`; its value on `𝓕` is denoted `𝓕|_{S_Zar}`. -/
@[stacks 04BS] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.inverseImage (𝟙 S) :
    Sheaf S.bigZariskiTopology (Type (u + 1)) ⥤
      Sheaf S.smallZariskiTopology (Type (u + 1)))
