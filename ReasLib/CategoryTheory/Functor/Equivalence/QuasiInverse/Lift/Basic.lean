/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Adjointification

/-!
# Functorial lifting through explicit quasi-inverses

This file owns the functor on functor categories induced by an explicit quasi-inverse, its
elementary computations, and preservation of equivalences.
-/

@[expose] public section

universe vA uA vB uB vE uE

namespace CategoryTheory.Functor.QuasiInverse

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {F : A ⥤ B}

/-- Postcomposition with an explicitly supplied quasi-inverse, regarded as a functor between
functor categories. This is the choice-explicit owner for constructions obtained by solving an
equivalence on the codomain side. The source category is explicit because it cannot be recovered
from `e`. -/
@[stacks 04W9 "functor-category lift along an explicit quasi-inverse"]
def liftFunctor (e : QuasiInverse F) (E : Type uE) [Category.{vE} E] :
    (E ⥤ B) ⥤ (E ⥤ A) :=
  (e.adjointifyUnit.congrRight (E := E)).inverse

namespace liftFunctor

variable {E : Type uE} [Category.{vE} E]

/-- Evaluating the lift functor at `G` is postcomposition of `G` by the supplied inverse. -/
@[simp]
theorem obj (e : QuasiInverse F) (G : E ⥤ B) :
    (e.liftFunctor E).obj G = G ⋙ e.inverse := sorry

/-- A lifted functor applies the chosen inverse functor to each input object. -/
@[simp]
theorem obj_obj (e : QuasiInverse F) (G : E ⥤ B) (X : E) :
    ((e.liftFunctor E).obj G).obj X = e.inverse.obj (G.obj X) := sorry

/-- A lifted functor maps a morphism by first applying the input functor and then the chosen
inverse functor. -/
@[simp]
theorem obj_map (e : QuasiInverse F) (G : E ⥤ B) {X Y : E} (f : X ⟶ Y) :
    ((e.liftFunctor E).obj G).map f = e.inverse.map (G.map f) := sorry

/-- The lift functor maps a natural transformation by applying the chosen inverse componentwise. -/
@[simp]
theorem map_app (e : QuasiInverse F) {G H : E ⥤ B} (α : G ⟶ H) (X : E) :
    ((e.liftFunctor E).map α).app X = e.inverse.map (α.app X) := sorry

/-- Lifting along explicit quasi-inverse data is itself an equivalence of functor categories. -/
theorem isEquivalence (e : QuasiInverse F) :
    (e.liftFunctor E).IsEquivalence := sorry

/-- Lifting an equivalence through explicit quasi-inverse data again gives an equivalence. The
equivalence proof for the input functor is kept as an ordinary argument, so callers need not
install a temporary instance. -/
theorem obj.isEquivalence (e : QuasiInverse F) (G : E ⥤ B)
    (hG : G.IsEquivalence) :
    ((e.liftFunctor E).obj G).IsEquivalence := sorry

end liftFunctor

/- Axiom audit: the lift functor is the inverse functor of mathlib's
`Equivalence.congrRight`; `sorryAx` occurs only in theorem-valued computation and equivalence
fields. -/

end CategoryTheory.Functor.QuasiInverse
