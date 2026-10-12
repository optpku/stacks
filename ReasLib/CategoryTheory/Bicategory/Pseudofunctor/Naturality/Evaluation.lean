/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
