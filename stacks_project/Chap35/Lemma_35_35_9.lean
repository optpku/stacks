/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback.Family.FullyFaithful
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Scheme.DescentData.Pullback

/- Lemma 35.35.9: if every fiber of a same-base morphism of scheme families is an fpqc
covering, then pullback of descent data along that morphism is fully faithful. -/
@[stacks 02VZ] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.fullyFaithfulOfFpqcFibers :
    {S : Scheme.{u}} →
      {𝒰 : SemiRepresentableFamily.Over.{v} S} →
        {𝒱 : SemiRepresentableFamily.Over.{w} S} →
          (φ : SemiRepresentableFamily.Over.Hom
            (SemiRepresentableFamily.Over.map (Over.map (𝟙 S)) 𝒰) 𝒱) →
            (∀ j : 𝒱.index, Scheme.FpqcCovering (φ.fiber j).obj) →
              Nonempty (functorOfHom φ).FullyFaithful)

end AlgebraicGeometry.Scheme.DescentData.Pullback
