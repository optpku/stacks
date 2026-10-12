/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Computations.Action
public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Computations.Identity
public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Computations.Composition

@[expose] public section

/-!
# Computation API for the pseudofunctor associated to a cleavage

This aggregate exposes the action, identity-comparison, and composition-comparison
normalization interfaces. Focused consumers may import the corresponding leaf module.
-/
