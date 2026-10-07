module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Reduced
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 35.19.1: If `f : X ⟶ Y` is flat and surjective and `X` is reduced, then
`Y` is reduced. -/
@[stacks 06QM] #check (AlgebraicGeometry.Flat.isReduced_of_surjective :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [IsReduced X], IsReduced Y)
