/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.FlatLocal
import StacksCheckRecall

/-!
# Cohen--Macaulayness Under Flat Local Base Change

@stack 00R5
-/

@[expose] public section

/- Lemma 10.112.9 (1) (Stacks tag `00R5`): a finite flat local algebra over
a Cohen--Macaulay Noetherian local ring is Cohen--Macaulay. -/
@[stacks 00R5 "(1)"]
#check @RingHom.Flat.cohenMacaulay_of_finite

/- Lemma 10.112.9 (2) (Stacks tag `00R5`): a finite flat local algebra map
preserves Krull dimension. -/
@[stacks 00R5 "(2)"]
#check @RingHom.Flat.ringKrullDim_eq_of_finite

/- Lemma 10.112.9 (3) (Stacks tag `00R5`): flat local base change preserves
Cohen--Macaulayness when the target dimension is at most the source
dimension. -/
@[stacks 00R5 "(3)"]
#check @RingHom.Flat.cohenMacaulay_of_ringKrullDim_le

/- Lemma 10.112.9 (4) (Stacks tag `00R5`): under the hypotheses of clause
(3), the source and target Krull dimensions agree. -/
@[stacks 00R5 "(4)"]
#check @RingHom.Flat.ringKrullDim_eq_of_ringKrullDim_le_of_cohenMacaulay
