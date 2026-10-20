/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Constant
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Adjunction
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.Opposite
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Constructions.AsSmall
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.GroupoidValued
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Composition

/-!
# Reusable pseudofunctor constructions

Compatibility aggregate for shape-independent constant diagrams and their mapped
comparison, the action on bicategories of adjunctions, bicategorical opposites,
universe resizing for `Cat`-valued pseudofunctors, invariant groupoid-valued
full subbicategories, and generic composition coherence. Limit-specific modules
should import the smallest corresponding leaf rather than rebuild its
transformation or coherence data.
-/
