/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution
import StacksCheckRecall

@[expose] public section

/- Lemma 13.19.4 is the K-projective null-homotopy theorem, specialized by
the canonical instance on `CochainComplex.ProjectiveMinus`. -/
@[stacks 0647] #check @CochainComplex.IsKProjective.nonempty_homotopy_zero
@[stacks 0647] #check @CochainComplex.Minus.TermsIn.instIsKProjective

end
