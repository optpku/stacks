/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Restricting functors to full subcategories

A functor carrying one object property into another restricts canonically to
the corresponding full subcategories.  This file owns the restriction data
and the inclusion-level computation API.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.FullSubcategory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {P : ObjectProperty C} {Q : ObjectProperty D}

/-- Restrict a functor to full subcategories selected by object properties
when it carries every source object satisfying `P` to an object satisfying
`Q`. -/
@[stacks 001D "restriction of a functor to full subcategories"]
def restrict (F : C ⥤ D) (hF : P ≤ Q.inverseImage F) :
    P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F) (fun X => hF X.obj X.property)

namespace restrict

/-- Forgetting a restricted functor recovers the ambient functor after the
source inclusion. -/
@[stacks 001D "inclusion comparison for a restricted functor"]
def compιIso (F : C ⥤ D) (hF : P ≤ Q.inverseImage F) :
    restrict F hF ⋙ Q.ι ≅ P.ι ⋙ F :=
  Q.liftCompιIso (P.ι ⋙ F) (fun X => hF X.obj X.property)

/-- Restricting a full functor to full subcategories remains full. -/
@[stacks 001D "fullness of a restricted functor"]
instance full (F : C ⥤ D) (hF : P ≤ Q.inverseImage F) [F.Full] :
    (restrict F hF).Full := sorry

/-- Restricting a faithful functor to full subcategories remains faithful. -/
@[stacks 001D "faithfulness of a restricted functor"]
instance faithful (F : C ⥤ D) (hF : P ≤ Q.inverseImage F) [F.Faithful] :
    (restrict F hF).Faithful := sorry

/-- The underlying object of a restricted functor is obtained by applying the
ambient functor. -/
@[simp]
theorem obj_obj (F : C ⥤ D) (hF : P ≤ Q.inverseImage F)
    (X : P.FullSubcategory) :
    ((restrict F hF).obj X).obj = F.obj X.obj := sorry

/-- The underlying morphism of a restricted functor is obtained by applying
the ambient functor. -/
@[simp]
theorem map_hom (F : C ⥤ D) (hF : P ≤ Q.inverseImage F)
    {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((restrict F hF).map f).hom = F.map f.hom := sorry

/-- The forward inclusion comparison is componentwise the identity. -/
@[simp]
theorem compιIso_hom_app (F : C ⥤ D) (hF : P ≤ Q.inverseImage F)
    (X : P.FullSubcategory) :
    (compιIso F hF).hom.app X = 𝟙 (F.obj X.obj) := sorry

/-- The inverse inclusion comparison is componentwise the identity. -/
@[simp]
theorem compιIso_inv_app (F : C ⥤ D) (hF : P ≤ Q.inverseImage F)
    (X : P.FullSubcategory) :
    (compιIso F hF).inv.app X = 𝟙 (F.obj X.obj) := sorry

end restrict

end CategoryTheory.ObjectProperty.FullSubcategory
