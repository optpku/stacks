module

import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution
import StacksCheckRecall

@[expose] public section

/-!
# Exercise 111.30.9

The source-facing existence of a degree-zero filtered-injective replacement of an object of
`Filᶠ(C)` is owned by `CochainComplex.FilteredInjectivePlus.exists_quasiIso_single` in ReasLib.
-/

namespace CochainComplex.FilteredInjectivePlus

/- Exercise 111.30.9: in an abelian category with enough injectives, every object of
`Filᶠ(C)` admits a morphism `A[0] ⟶ I^•` to a complex of finite filtered-injective objects
that vanishes in negative degrees and is a filtered quasi-isomorphism. -/
@[stacks 028G] #check
  @exists_quasiIso_single

end CochainComplex.FilteredInjectivePlus
