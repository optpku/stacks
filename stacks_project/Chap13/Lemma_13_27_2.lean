/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Ext.Resolution
import StacksCheckRecall

@[expose] public section

/-!
## Lemma 13.27.2 (Stacks Project, 06XR)

The injective and projective resolution computation maps are owned by
`CochainComplex.InjectiveResolution` and `CochainComplex.ProjectiveResolution`.  This entry
recalls the direct APIs without chapter-local type or theorem aliases.
-/

#check @CochainComplex.InjectiveResolution
@[stacks 06XR] #check @CochainComplex.InjectiveResolution.resolutionAddEquiv
@[stacks 06XR] #check @CochainComplex.InjectiveResolution.homotopyAddEquiv
@[stacks 06XR] #check @CochainComplex.InjectiveResolution.extAddEquiv
@[stacks 06XR] #check @CochainComplex.InjectiveResolution.extAddEquiv_apply
@[stacks 06XR] #check @CochainComplex.InjectiveResolution.extAddEquiv_symm_apply
#check @CochainComplex.ProjectiveResolution
@[stacks 06XR] #check @CochainComplex.ProjectiveResolution.resolutionAddEquiv
@[stacks 06XR] #check @CochainComplex.ProjectiveResolution.homotopyAddEquiv
@[stacks 06XR] #check @CochainComplex.ProjectiveResolution.extAddEquiv
@[stacks 06XR] #check @CochainComplex.ProjectiveResolution.extAddEquiv_apply
@[stacks 06XR] #check @CochainComplex.ProjectiveResolution.extAddEquiv_symm_apply
#check @CochainComplex.IsKInjective.homAddEquiv_naturality_left
#check @CochainComplex.IsKInjective.homAddEquiv_naturality_right
#check @CochainComplex.IsKProjective.homAddEquiv_naturality_left
#check @CochainComplex.IsKProjective.homAddEquiv_naturality_right
