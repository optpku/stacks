/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Existence
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.21.2

Existence of Cartan--Eilenberg resolutions is owned by the neutral cochain-complex API.
-/

/- Lemma 13.21.2: every bounded-below cochain complex in an abelian category with enough
injectives admits a Cartan--Eilenberg resolution. -/
@[stacks 015I] #check @CochainComplex.CartanEilenbergResolution.nonempty
