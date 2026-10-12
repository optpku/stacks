/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.GroupoidDescent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigHSite.GroupoidDescent

/- Lemma 38.37.13: a category fibred in groupoids on a chosen big h-site
slice is an h-stack if and only if it has Zariski descent, descent along
affine-target surjective flat proper morphisms of finite presentation, and
descent for the principal-center and two-generator almost-blow-up families. -/
@[stacks 0EX9] #check
  (AlgebraicGeometry.ChosenBigHSite.GroupoidDescent.iffZariskiAndFlatProperExampleDescent :
    ∀ (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)
      (𝒮 : FiberedCategoryOver.Groupoids.{max u v, v, max u v, max u v} (Over S)),
      IsStack.InGroupoids (bigTopology Schh S) 𝒮.p ↔
        IsStack.InGroupoids (bigZariskiTopology Schh S) 𝒮.p ∧
          IsAffineFlatProperSurjective Schh S 𝒮 ∧
            IsPrincipalCenter Schh S 𝒮 ∧ IsTwoGenerator Schh S 𝒮)

end AlgebraicGeometry.ChosenBigHSite.GroupoidDescent
