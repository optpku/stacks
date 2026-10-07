module

public import Mathlib.AlgebraicGeometry.Restrict
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.9.2: open immersions into schemes and open subsets of schemes carry the canonical
induced scheme structures. -/
@[stacks 01IK] #check PresheafedSpace.IsOpenImmersion.toScheme
#check PresheafedSpace.IsOpenImmersion.toScheme_toLocallyRingedSpace
#check LocallyRingedSpace.IsOpenImmersion.isoRestrict
@[stacks 01IK "open subscheme"] #check Scheme.Opens.toScheme
#check Scheme.Opens.ι
