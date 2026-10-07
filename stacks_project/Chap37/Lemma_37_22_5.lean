module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.22.5 (1): a flat morphism from a Cohen--Macaulay scheme to a
locally Noetherian scheme is Cohen--Macaulay. -/
@[stacks 0C0X] #check
  (AlgebraicGeometry.CohenMacaulay.of_flat_of_source :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Scheme.CohenMacaulay X]
      [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.Flat f],
      AlgebraicGeometry.CohenMacaulay f)

/- Lemma 37.22.5 (2): under the same hypotheses, the target stalk at every
point in the image of the morphism is Cohen--Macaulay. -/
@[stacks 0C0X] #check
  (AlgebraicGeometry.Scheme.CohenMacaulay.instTargetStalkOfFlat :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.Scheme.CohenMacaulay X]
      [AlgebraicGeometry.IsLocallyNoetherian Y] [AlgebraicGeometry.Flat f]
      (x : X),
      CohenMacaulayRing (Y.presheaf.stalk (f x)))
