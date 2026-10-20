/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation.At
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation.Action
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Evaluation.Pseudofunctor

/-!
# Evaluation of pseudofunctors

Compatibility aggregate for point evaluation, its source-morphism action, and
the curried bicategorical evaluation pseudofunctor. Focused developments should
import the smallest relevant `Evaluation.At`, `Evaluation.Action`, or
`Evaluation.Pseudofunctor` leaf.
-/
