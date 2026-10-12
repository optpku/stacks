/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Derivation.Extension
import StacksCheckRecall

/-!
# Extending derivations

Lemma 15.48.1 is recalled through the shared extension API.  The formal statements use
commutative rings, matching the ambient localization and adic-completion owners.

@stack 07PE
-/

@[expose] public section

/- Lemma 15.48.1 (1): an absolute derivation extends uniquely to every adic completion. -/
@[stacks 07PE "Lemma 15.48.1 (1)"]
#check @Derivation.Extension.existsUnique_adicCompletion

/- Lemma 15.48.1 (2): an absolute derivation extends uniquely to every localization. -/
@[stacks 07PE "Lemma 15.48.1 (2)"]
#check @Derivation.Extension.existsUnique_localization

/- Lemma 15.48.1 (3): after an away-localization identification, a suitable power multiple of
the derivation extends across a finite-type algebra. -/
@[stacks 07PE "Lemma 15.48.1 (3)"]
#check @Derivation.Extension.exists_pow_smul_of_finiteType_awayIso
