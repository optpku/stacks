/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution.Functoriality
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.29.3

The reusable owner is the lower-truncation resolution tower in ReasLib.  Its
under-category presentation retains the canonical truncation comparison,
termwise split epimorphisms, and the degreewise kernel condition without
making Chapter 13 own a second representation of that data.
-/

/- Lemma 13.29.3 (Stacks 070F): lower-truncation resolution towers are the
source-facing data of the construction. -/
@[stacks 070F] #check @CochainComplex.LowerTruncation.Resolution

/- The lower-truncation inverse system is functorial in the original complex,
with components given by `CochainComplex.truncGEMap`. -/
@[stacks 070F] #check @CochainComplex.LowerTruncation.diagramFunctor

/- Lemma 13.29.3 (Stacks 070F): under the stated object-property hypotheses,
every cochain complex admits such a resolution tower. -/
@[stacks 070F] #check @CochainComplex.LowerTruncation.exists_resolution
