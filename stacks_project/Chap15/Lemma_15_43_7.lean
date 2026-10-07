module

import StacksCheckRecall
public import ReasLib.RingTheory.Completion.FaithfullyFlat
public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Normal

@[expose] public section

/-!
# Lemma 15.43.7

@stack 0FIZ
-/

open IsLocalRing

universe u

/- Lemma 15.43.7 (0FIZ): if the maximal-ideal adic completion of a Noetherian local ring `A` is
normal, then `A` is normal.  The source-facing entry is a direct specialization of the reusable
faithfully-flat descent API; no chapter-owned wrapper is needed. -/
@[stacks 0FIZ "normality descends from maximal-ideal completion"]
#check fun (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsNormalRing (AdicCompletion (maximalIdeal A) A)] ↦
  RingHom.FaithfullyFlat.isNormalRing
    (AdicCompletion.maximalIdeal_algebraMap_faithfullyFlat A)
