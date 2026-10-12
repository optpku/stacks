/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normal.Serre
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.157.4: Serre's criterion for normality

The reusable theorem is owned by `ReasLib.RingTheory.Normal.Serre`.  This
chapter file keeps the source label as a thin bridge, so later chapters can
use the canonical owner without importing Chapter 10.

@stack 031S
-/

/- Lemma 10.157.4 (Stacks tag `031S`): a Noetherian commutative ring is normal exactly when it
satisfies Serre's conditions `(R₁)` and `(S₂)`.  The reusable owner already exposes this
equivalence in the `IsNormalRing` namespace. -/
@[stacks 031S]
#check @IsNormalRing.iff_serre
