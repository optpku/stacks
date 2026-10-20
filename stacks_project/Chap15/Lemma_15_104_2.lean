/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.CoaugmentedResolution
import Mathlib.Algebra.Category.Grp.Abelian
import StacksCheckRecall

/-!
# Lemma 15.104.2

The source statement is the columnwise quasi-isomorphism criterion from the reusable product-total
API.

@stack 0EYX
-/

@[expose] public section

open CategoryTheory Limits ComplexShape HomologicalComplex HomologicalComplex₂
open scoped HomologicalComplex₂

noncomputable section

/- Lemma 15.104.2 (0EYX): a map of complexes of complexes of abelian groups whose columns are
quasi-isomorphisms induces a quasi-isomorphism on product totals. The owner is stated for an
abelian category with exact countable products and this check records the source specialization
`C := AddCommGrpCat`. -/
@[stacks 0EYX "columnwise quasi-isomorphisms induce product-total quasi-isomorphisms"]
#check @HomologicalComplex₂.CoaugmentedResolution.ProductTotal.map_quasiIso_of_columnwise
@[stacks 0EYX "abelian-group specialization of columnwise quasi-isomorphisms"]
#check @HomologicalComplex₂.CoaugmentedResolution.ProductTotal.map_quasiIso_of_columnwise
  (C := AddCommGrpCat)
