/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Immersion

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.24.2: a closed embedding whose structure-sheaf map is locally
surjective is a closed immersion. -/
@[stacks 01LD]
#check IsClosedImmersion.of_isClosedEmbedding_of_isLocallySurjective

#check IsClosedImmersion.of_isClosedEmbedding_of_surjectiveOnStalks
#check isClosedImmersion_iff
