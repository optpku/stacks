module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Length.Local
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.55.7

The length isomorphism for the finite-module Grothendieck group of an Artinian local ring is
recalled from its ReasLib owner.

@stack 00JI
-/

/- Lemma 10.55.7: for an Artinian local ring `R`, the composition-length map
`ModuleCat.K0.finiteLength R : ModuleCat.K0.finite R →+ ℤ` is an isomorphism. -/
@[stacks 00JI "finite-length map is bijective"]
#check @CategoryTheory.ModuleCat.K0.finiteLength_bijective

/- The corresponding canonical additive equivalence has inverse given by virtual multiples of the
residue-field class. -/
@[stacks 00JI "finite-length equivalence"]
#check @CategoryTheory.ModuleCat.K0.finiteLengthEquiv

@[stacks 00JI "inverse on virtual residue-field classes"]
#check @CategoryTheory.ModuleCat.K0.finiteLengthEquiv_symm_apply
