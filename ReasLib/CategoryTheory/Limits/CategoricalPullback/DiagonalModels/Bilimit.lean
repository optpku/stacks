/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Bilimit
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.DiagonalModels.Comparison
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.DiagonalModels.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bilimit comparisons with the iterated diagonal model

The equivalence criterion for the specified comparison from a bilimit square to the iterated
concrete model.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Prod
open CategoricalPullback
open CategoricalPullback.CatCommSqOver

universe v u

namespace CategoryTheory.Limits

variable {C : Type (max u v)} [Category.{v} C]
variable {S : Type (max u v)} [Category.{v} S]
variable {G₁ G₂ : C ⥤ S}
variable {C' : Type (max u v)} [Category.{v} C']
variable (P : CatCommSqOver (G₁.prod' G₂) (Functor.diag S) C')

namespace CategoricalPullback.CatCommSqOver.iteratedDiagonalComparison

/-- If `P` is a bilimit square over `G₁.prod' G₂` and `Functor.diag S`, its specified comparison
to the iterated diagonal categorical-pullback model
`((π₁ G₁ G₂).prod' (π₂ G₁ G₂)) ⊡ Functor.diag C` is an equivalence.

An explicit inverse is intentionally not a second public owner here: an inverse to
`P.comparison` is selected from the universal property, whereas the concrete-model inverse is
deterministic. Consumers needing such a choice can use
`P.iteratedDiagonalComparison.asEquivalence`. -/
@[stacks 02XF "diagonal iterated-pullback comparison equivalence"]
instance isEquivalence
    [P.IsBilimit] :
    P.iteratedDiagonalComparison.IsEquivalence := sorry

end CategoricalPullback.CatCommSqOver.iteratedDiagonalComparison

end CategoryTheory.Limits
