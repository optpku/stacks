module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Stalk

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.13.1: morphisms `Spec R ⟶ X`, for a local ring `R`, are
equivalent to a point `x : X` together with a local map `𝒪_{X,x} ⟶ R`. -/
@[stacks 01J6] #check SpecToEquivOfLocalRing

#check SpecToEquivOfLocalRing_apply_fst
#check SpecToEquivOfLocalRing_apply_snd_coe
