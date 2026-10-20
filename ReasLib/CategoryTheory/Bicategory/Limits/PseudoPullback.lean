/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Pseudofunctor
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Presentation
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Hom
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Modification
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.TransformationFunctor
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Functoriality
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Functoriality.Computations
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Postcompose
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Pith
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Pith.Symmetry
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Pith.Biterminal
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Hom
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Symmetry
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Symmetry.Biterminal
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Diagonal
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LeftLegDiagonal
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Factorization
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.HomProperty
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Induced
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ProjectionEquivalence
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudolimit

/-!
# Bicategorical pseudopullbacks

This compatibility import assembles the reusable pseudopullback API from its semantic owners.
`Cospan` owns bundled walking-cospan data and its componentwise maps; `PseudoPullback` leaves
own readable cone presentations, diagonal and edge-factorization operations, square
postcomposition, bilimits, changes of cospan, lifts, symmetry, and induced bicategories;
`CategoricalPullback` owns the bridge to ordinary categorical pullbacks in `Cat`.

Focused downstream developments should import the smallest relevant leaf. This root remains for
the historical broad import path and does not reintroduce a parallel implementation.
-/
