/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Functorial
import StacksCheckRecall

@[expose] public section

/-!
# Remark 13.24.2

The source description is a compatibility statement, not a second construction of resolutions.
The reusable owner is the homotopy realization of a strict functorial injective resolution.
-/

/- Remark 13.24.2 (Stacks 05TL): after passing to the bounded-below homotopy category, the
resolution functor induced by a strict choice agrees, up to its canonical natural isomorphism,
with the target functor of the chosen injective-resolution arrows. -/
@[stacks 05TL] #check @CochainComplex.FunctorialInjectiveResolution.nonempty_homotopyRealization

#check @CochainComplex.FunctorialInjectiveResolution.HomotopyRealization.targetIso
#check @CochainComplex.FunctorialInjectiveResolution.HomotopyRealization.targetIso_fac
#check @CochainComplex.FunctorialInjectiveResolution.HomotopyRealization.targetIso_unique
