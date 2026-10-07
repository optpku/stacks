module

public import stacks_project.Chap75.Lemma_75_6_5_ProjectionFormula
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory

universe u

/- Lemma 75.6.5: for an affine morphism `f : X ⟶ Y` of algebraic spaces over `S`
and `E` in `D_QCoh(𝒪_Y)`, the object `Rf_* Lf^* E` is isomorphic to
`E ⊗ᴸ f_* 𝒪_X`. -/
@[stacks 08IJ] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.affinePushforwardPullback_isomorphic :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
      (E : DerivedQCoh Y),
      IsIsomorphic ((pushforward f).obj ((pullback f).obj E))
        (tensorObj E (pushforwardStructureSheaf f)))
