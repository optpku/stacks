module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Pullbacks

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/- Definition 26.17.1: the fibre product of `f` and `g` is the categorical
pullback, with its canonical projections and universal property. -/
@[stacks 01JP] #check pullback f g
#check pullback.fst f g
#check pullback.snd f g
#check pullbackIsPullback f g
