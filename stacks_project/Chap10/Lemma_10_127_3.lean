/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.FinitePresentation.FilteredColimit
import StacksCheckRecall

@[expose] public section

/-!
# Finite Presentation and Filtered Colimits

The reusable `RingHom.FinitePresentation` characterization is the canonical
owner of this textbook entry.

@stack 00QO
-/

-- Lemma 10.127.3, tag `00QO`: finite presentation of `R → S`, preservation
-- of filtered colimits by `Hom_R(S, -)`, and stagewise factorization through
-- filtered colimits are equivalent.
@[stacks 00QO]
#check @RingHom.FinitePresentation.tfae
