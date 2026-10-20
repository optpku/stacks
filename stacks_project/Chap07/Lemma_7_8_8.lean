/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Precoverage.Combinatorial

/-!
# Lemma 7.8.8

The source compares two site presentations contained in one ambient class of
coverings.  ReasLib records the exact precoverage-level hypothesis, rather
than incorrectly strengthening it to equality of the three covering classes.
-/

@[expose] public section

/- Lemma 7.8.8 (00VY): if `K₁` and `K₂` are sub-precoverages of `K`, and every
`K`-cover has combinatorially equivalent replacements in both, then the two
sub-precoverages define the same sheaf theory. -/
@[stacks 00VY] #check @CategoryTheory.Precoverage.toGrothendieck_eq_of_common_ambient_covers

@[stacks 00VY] #check @CategoryTheory.Precoverage.isSheaf_iff_of_common_ambient_covers
