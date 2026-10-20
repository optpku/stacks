/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Lift.Choice

/-!
# Diagram lifting through explicit quasi-inverses

This file lifts a diagram of functors through an explicit quasi-inverse.  It owns the natural
comparison with the original diagram and the canonical independence of the quasi-inverse data.
-/

@[expose] public section

universe vA uA vB uB vE uE vK uK

namespace CategoryTheory.Functor.QuasiInverse.liftFunctor

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {E : Type uE} [Category.{vE} E]
variable {K : Type uK} [Category.{vK} K]
variable {F : A ⥤ B}

/-- Lift every functor in a diagram through an explicitly supplied quasi-inverse. The source
category `E` is inferred from the codomain of `P`. -/
@[stacks 04W9 "diagram lift along an explicit quasi-inverse"]
def diagram (e : QuasiInverse F) (P : K ⥤ (E ⥤ B)) : K ⥤ (E ⥤ A) :=
  P ⋙ e.liftFunctor E

namespace diagram

/-- The lifted diagram followed by the original functor is naturally isomorphic to the input
diagram. -/
@[stacks 04W9 "comparison for a diagram lift"]
def comparisonIso (e : QuasiInverse F) (P : K ⥤ (E ⥤ B)) :
    diagram e P ⋙ (Functor.whiskeringRight E A B).obj F ≅ P :=
  Functor.associator P (e.liftFunctor E)
      ((Functor.whiskeringRight E A B).obj F) ≪≫
    Functor.isoWhiskerLeft P (comparisonNatIso e E) ≪≫
    P.rightUnitor

/-- The component of the diagram comparison is the pointwise quasi-inverse lift comparison. -/
@[simp, stacks 04W9 "component of a diagram lift comparison"]
theorem comparisonIso.app (e : QuasiInverse F) (P : K ⥤ (E ⥤ B)) (k : K) :
    (comparisonIso e P).app k = liftFunctor.comparisonIso e (P.obj k) := sorry

/-- Changing the explicit quasi-inverse gives a canonical isomorphism between the lifted
diagrams. -/
@[stacks 04W9 "choice independence of a diagram lift"]
def choiceIso (e e' : QuasiInverse F) (P : K ⥤ (E ⥤ B)) :
    diagram e P ≅ diagram e' P :=
  Functor.isoWhiskerLeft P (choiceNatIso e e' E)

/-- The component of diagram-level choice independence is pointwise choice independence. -/
@[simp, stacks 04W9 "component of diagram lift choice independence"]
theorem choiceIso.app (e e' : QuasiInverse F) (P : K ⥤ (E ⥤ B)) (k : K) :
    (choiceIso e e' P).app k = liftFunctor.choiceIso e e' (P.obj k) := sorry

/-- Choice independence preserves the comparison with the original diagram. -/
@[stacks 04W9 "diagram lift choice comparison coherence"]
theorem choiceIso.comparison (e e' : QuasiInverse F) (P : K ⥤ (E ⥤ B)) :
    Functor.isoWhiskerRight (choiceIso e e' P)
          ((Functor.whiskeringRight E A B).obj F) ≪≫
        comparisonIso e' P =
      comparisonIso e P := sorry

/-- The choice comparison from a diagram lift to itself is the identity. -/
@[simp, stacks 04W9 "identity diagram lift choice comparison"]
theorem choiceIso.refl (e : QuasiInverse F) (P : K ⥤ (E ⥤ B)) :
    choiceIso e e P = Iso.refl (diagram e P) := sorry

/-- Reversing a diagram choice comparison exchanges the two quasi-inverses. -/
@[simp, stacks 04W9 "symmetric diagram lift choice comparison"]
theorem choiceIso.symm (e e' : QuasiInverse F) (P : K ⥤ (E ⥤ B)) :
    (choiceIso e e' P).symm = choiceIso e' e P := sorry

/-- Diagram choice comparisons compose transitively. -/
@[stacks 04W9 "composition of diagram lift choice comparisons"]
theorem choiceIso.trans (e e' e'' : QuasiInverse F) (P : K ⥤ (E ⥤ B)) :
    choiceIso e e' P ≪≫ choiceIso e' e'' P = choiceIso e e'' P := sorry

/- Axiom audit: the lifted diagram and both isomorphisms are composites and whiskerings of
explicit functorial data. The statement-stage debt is confined to computation and coherence
theorems. -/

end diagram

end CategoryTheory.Functor.QuasiInverse.liftFunctor
