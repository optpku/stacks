/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.ContentIdeal.MittagLeffler

/-!
# Lemma 15.24.4

Existence and uniqueness of content ideals for flat Mittag-Leffler modules are
recalled from their shared owner.

@stack 0ASD
-/

@[expose] public section

universe u v

/- Lemma 15.24.4: every element of a flat Mittag-Leffler module has a content
ideal. -/
@[stacks 0ASD "Lemma 15.24.4"]
#check fun (A : Type u) (M : Type v) [CommRing A] [AddCommGroup M]
    [Module A M] [Module.Flat A M] [Module.MittagLeffler A M] (x : M) ↦
  Module.MittagLeffler.exists_contentIdeal (A := A) x

/- The reusable leaf also records uniqueness. -/
#check @Module.MittagLeffler.existsUnique_contentIdeal
