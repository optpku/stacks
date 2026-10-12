/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Slice.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Slice.ExtendRestrict
public import ReasLib.CategoryTheory.Fibered.Stack.Slice.Presentation

/-!
# Stacks on a slice site

This compatibility import exposes the basic slice presentations, extension and restriction,
the presentation equivalence, and localization as a strict slice over a representable stack.
Focused downstream files may instead import the corresponding `Slice` submodule directly.
-/
