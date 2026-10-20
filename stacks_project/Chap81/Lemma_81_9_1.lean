module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ElementaryDistinguishedSquare.Pushout
import StacksCheckRecall

/-!
# Lemma 81.9.1

The fibre-product square of an elementary distinguished square of algebraic
spaces over a scheme `S` is a pushout in `AlgebraicSpace S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 81.9.1. Let `S` be a scheme. Let `(U ⊂ W, f : V ⟶ W)` be an elementary
distinguished square of algebraic spaces over `S`. Then the fibre-product square
`U ×_W V ⟶ V`, `U ×_W V ⟶ U`, `U ⟶ W`, `V ⟶ W` is a pushout in `AlgebraicSpace S`. -/
@[stacks 0DVI] #check
  (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare.isPushout :
    ∀ {S : Scheme.{u}} {P U V W : AlgebraicSpace S}
      (j : U ⟶ W) (f : V ⟶ W) {pU : P ⟶ U} {pV : P ⟶ V}
      [IsElementaryDistinguishedSquare j f],
      IsPullback pU pV j f → IsPushout pU pV j f)

/- The chosen fibre product `U ×_W V` of an elementary distinguished square
`(j : U ⟶ W, f : V ⟶ W)` is a pushout square in `AlgebraicSpace S`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare.isPushout_pullback :
    ∀ {S : Scheme.{u}} {U V W : AlgebraicSpace S}
      (j : U ⟶ W) (f : V ⟶ W) [IsElementaryDistinguishedSquare j f],
      IsPushout (pullback.fst j f) (pullback.snd j f) j f)
