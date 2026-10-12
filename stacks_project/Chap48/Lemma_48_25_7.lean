/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 48.25.7 (1): a flat morphism from a Gorenstein scheme to a locally
Noetherian scheme is Gorenstein. -/
@[stacks 0C12] #check
  (AlgebraicGeometry.Gorenstein.of_flat_of_source :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
        [Scheme.Gorenstein X] [IsLocallyNoetherian Y] [Flat f],
      Gorenstein f)

/- Lemma 48.25.7 (2): every target stalk at an image point of such a morphism
is a Gorenstein local ring. -/
@[stacks 0C12] #check
  (AlgebraicGeometry.Scheme.Gorenstein.instTargetStalkOfFlat :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
        [Scheme.Gorenstein X] [IsLocallyNoetherian Y] [Flat f] (x : X),
      IsGorensteinLocalRing (Y.presheaf.stalk (f x)))

end AlgebraicGeometry
