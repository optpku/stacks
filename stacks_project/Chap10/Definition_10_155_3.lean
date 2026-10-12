/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
import StacksCheckRecall

@[expose] public section

/-!
# Names for henselizations

Definition 10.155.3 introduces terminology for the maps constructed in the
two preceding existence lemmas.  The right formal owner is consequently the
intrinsic map property, rather than a construction-specific carrier or a
second wrapper around it.

@stack 04GQ
-/

/- Definition 10.155.3 (1), tag `04GQ`: a local map satisfying
`IsHenselizationOf R S` is called a henselization of `R`.  This intrinsic
property is the formal replacement for referring to the particular colimit
construction in Lemma 10.155.1. -/
@[stacks 04GQ "henselization of a local ring"]
recall IsHenselizationOf

/- Definition 10.155.3 (2)-(3), tag `04GQ`: a local map satisfying
`IsStrictHenselizationOf R S` is called a strict henselization of `R`.  The
chosen separable closure in Lemma 10.155.2 is construction data; the
intrinsic owner is the reusable downstream interface. -/
@[stacks 04GQ "strict henselization of a local ring"]
recall IsStrictHenselizationOf
