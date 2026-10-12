/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Shift.Right
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Shift.Left

@[expose] public section

/-!
# Shift-Compatible Domains of Pointwise Derived Functors

Convenience import for the right- and left-derived shift APIs.  The directional leaves remain
available to consumers that need only one Kan-extension variance.
-/
