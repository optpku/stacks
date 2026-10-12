/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Computations.Action
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Computations.Naturality
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Computations.Comparisons

/-!
# Pseudofunctor computations for based inertia

Compatibility aggregate for object/`1`-cell, `2`-cell, and local-hom action computations,
section/forgetful naturality, and identity/composition comparison computations of the ordinary
based-inertia pseudofunctor. Import `Computations.Action.{Objects,TwoCell,LocalAction}` directly
when only one action layer is needed.
-/
