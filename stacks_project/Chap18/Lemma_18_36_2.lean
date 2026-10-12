/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Sheaves.AddCommGrpCat
import StacksCheckRecall

/-!
# Abelian-group-valued stalk functors at a point of a site

This directly reuses the canonical Mathlib point-fiber API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{max u v} C]
variable (p : GrothendieckTopology.Point.{max u v} J)

/- Lemma 18.36.2 (1): the stalk functor on abelian sheaves is exact. -/
@[stacks 04EP "(1)"]
#check
  (ExactFunctor.of p.sheafFiber :
    Sheaf J AddCommGrpCat ⥤ₑ AddCommGrpCat)

/- Lemma 18.36.2 (2): the stalk functor on abelian presheaves is exact. -/
@[stacks 04EP "(2)"]
#check
  (ExactFunctor.of p.presheafFiber :
    (Cᵒᵖ ⥤ AddCommGrpCat) ⥤ₑ AddCommGrpCat)

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat]

/- Lemma 18.36.2 (3): an abelian presheaf and its sheafification have canonically isomorphic
stalks. -/
@[stacks 04EP "(3)"]
#check
  (p.presheafToSheafCompSheafFiberIso AddCommGrpCat :
    presheafToSheaf J AddCommGrpCat ⋙ p.sheafFiber ≅ p.presheafFiber)

end Sheafification

end CategoryTheory
