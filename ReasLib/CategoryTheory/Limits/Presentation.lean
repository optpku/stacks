/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Presentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Restricted colimit presentations

A colimit presentation can be restricted to a subset of a preorder-indexed diagram. The
resulting cocone is explicit data; whether it remains colimiting is a separate reusable
property.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {I : Type w} [Preorder I] {X : C}

/-- The cocone obtained by restricting a preorder-indexed colimit presentation to a subset of
its stages. -/
@[stacks 059W "restricted presentation cocone"]
def ColimitPresentation.restrictCocone
    (P : ColimitPresentation I X) (S : Set I) :
    Cocone ((OrderEmbedding.subtype S).toOrderHom.toFunctor ⋙ P.diag) :=
  P.cocone.whisker (OrderEmbedding.subtype S).toOrderHom.toFunctor

/-- The restricted cocone of `P` is again a colimit cocone.  `Nonempty` forgets the
contractible choice of universal lift while retaining the mathematical existence assertion. -/
@[stacks 059W "restricted presentation colimit"]
def ColimitPresentation.IsColimitRestriction
    (P : ColimitPresentation I X) (S : Set I) : Prop :=
  Nonempty (IsColimit (P.restrictCocone S))

end CategoryTheory.Limits
