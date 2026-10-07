module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.CohomologyBasis

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived.Pushforward.CohomologyBasis
open scoped CartesianClosed DerivedExt

/- Lemma 20.45.2 (0D66): basiswise negative hypercohomology of a derived module on inverse-image
opens implies (1) negative cohomology of its derived pushforward vanishes, (2) the same vanishing
on every open, (3) the degree-zero preimage cohomology presheaf is a sheaf, (4) negative local Ext
vanishing extends to every open, and (5) the degree-zero local derived-Hom presheaf is a sheaf. -/
@[stacks 0D66 "negative cohomology of a derived pushforward"]
#check @Negative.underlyingPushforwardIsZero

@[stacks 0D66 "negative preimage hypercohomology on every open"]
#check @Negative.allOpens

@[stacks 0D66 "sheafness of degree-zero preimage cohomology"]
#check @Negative.zeroIsSheaf

@[stacks 0D66 "negative local Ext on every open"]
#check @NegativeExt.allOpens

@[stacks 0D66 "sheafness of the degree-zero local derived-Hom presheaf"]
#check @NegativeExt.zeroInternalHomIsSheaf

@[stacks 0D66 "basiswise negative preimage cohomology condition"]
#check @Negative
@[stacks 0D66 "basiswise preimage cohomology presheaf vanishing"]
#check @Negative.presheafObjIsZero
@[stacks 0D66 "negative derived pushforward cohomology"]
#check @Negative.pushforwardIsZero
@[stacks 0D66 "negative preimage cohomology presheaf on every open"]
#check @Negative.presheafAllOpens
@[stacks 0D66 "basiswise negative Ext condition"]
#check @NegativeExt
@[stacks 0D66 "negative Ext for restricted representatives"]
#check @NegativeExt.iffRepresentative
@[stacks 0D66 "negative Ext as internal-Hom cohomology"]
#check @NegativeExt.toInternalHom
@[stacks 0D66 "preimage degree-zero derived-Hom comparison"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.RHom.Cohomology.preimageH0_isomorphic_restrictionHom
@[stacks 0D66 "preimage degree-zero representative derived-Hom comparison"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.RHom.Cohomology.preimageH0_isomorphic_representativeHom

end
