/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Preimage.Lift.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Operations on selected-preimage lifts

Identity, composition, and equality transport operate on explicit lifts between the selected
cochain representatives of derived objects.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.Preimage.Lift

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The canonical selected-preimage lift of an identity derived morphism. -/
@[stacks 0BKM "identity lift between selected derived-category preimages"]
noncomputable def id (K : DerivedCategory A) : Lift (𝟙 K) where
  hom := 𝟙 (DerivedCategory.Q.objPreimage K)
  comm := sorry

/-- Composition of selected-preimage lifts. -/
@[stacks 0BKM "composition of selected-preimage lifts"]
noncomputable def comp
    {K L M : DerivedCategory A} {f : K ⟶ L} {g : L ⟶ M}
    (l : Lift f) (m : Lift g) : Lift (f ≫ g) where
  hom := l.hom ≫ m.hom
  comm := sorry

/-- Transport a selected-preimage lift along an equality of derived morphisms. -/
@[stacks 0BKM "equality transport of a selected-preimage lift"]
noncomputable def reindex
    {K L : DerivedCategory A} {f g : K ⟶ L} (h : f = g) (l : Lift f) : Lift g where
  hom := l.hom
  comm := sorry

/-- The cochain map carried by the identity lift. -/
@[simp, stacks 0BKM "identity selected-preimage lift computation"]
theorem id_hom (K : DerivedCategory A) :
    (id K).hom = 𝟙 (DerivedCategory.Q.objPreimage K) := sorry

/-- The cochain map carried by a composite lift. -/
@[simp, stacks 0BKM "composite selected-preimage lift computation"]
theorem comp_hom
    {K L M : DerivedCategory A} {f : K ⟶ L} {g : L ⟶ M}
    (l : Lift f) (m : Lift g) :
    (comp l m).hom = l.hom ≫ m.hom := sorry

/-- Equality transport does not change the underlying cochain map. -/
@[simp, stacks 0BKM "transported selected-preimage lift computation"]
theorem reindex_hom
    {K L : DerivedCategory A} {f g : K ⟶ L} (h : f = g) (l : Lift f) :
    (reindex h l).hom = l.hom := sorry

/-- Two lifts of the same derived morphism are equal when their cochain maps are equal. -/
@[ext, stacks 0BKM "extensionality of selected-preimage lifts"]
theorem ext
    {K L : DerivedCategory A} {f : K ⟶ L} {l l' : Lift f}
    (h : l.hom = l'.hom) : l = l' := sorry

end CategoryTheory.DerivedCategory.Preimage.Lift
