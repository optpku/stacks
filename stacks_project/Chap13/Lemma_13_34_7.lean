/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.KInjective.Replacement
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.34.7

The source assertion is the non-functorial K-injective replacement theorem.
Its lower-truncation and Milnor-limit proof is internal to the neutral
K-injective replacement API, so the chapter entry remains a tagged recall
rather than a duplicate construction.
-/

/- Lemma 13.34.7 (Stacks 090Y): enough injectives and exact countable products
give a quasi-isomorphism from every cochain complex to a K-injective complex. -/
@[stacks 090Y] #check @CochainComplex.IsKInjective.exists_quasiIso

/- The bundled ReasLib owner installs both the K-injectivity and quasi-isomorphism witnesses for
downstream typeclass search. -/
#check @CochainComplex.KInjectiveResolution.nonempty
