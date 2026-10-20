module

public import ReasLib.CategoryTheory.Pro.Sequential.Realization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Common-refinement classes of sequential pro-morphisms

Two monotone representatives define the same pro-morphism exactly when they agree after a common
refinement.  This leaf owns the relation, its quotient, and the canonical comparison with the
actual Hom-set in `Pro C`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.Pro.SequentialHom

variable {C : Type u} [Category.{v} C] {X Y : ℕᵒᵖ ⥤ C}

/-- Two sequential representatives are equivalent when their level maps agree after passage to
one common monotone refinement. -/
def Equivalent (r₁ r₂ : Pro.SequentialHom X Y) : Prop :=
  ∃ (reindex : ℕ →o ℕ) (h₁ : r₁.reindex ≤ reindex) (h₂ : r₂.reindex ≤ reindex),
    (r₁.refine reindex h₁).hom = (r₂.refine reindex h₂).hom

/-- Composing with the identity representative on the right is neutral up to common refinement. -/
theorem comp_id_equivalent (r : Pro.SequentialHom X Y) :
    Equivalent (comp r (id Y)) r := sorry

/-- Composing with the identity representative on the left is neutral up to common refinement. -/
theorem id_comp_equivalent (r : Pro.SequentialHom X Y) :
    Equivalent (comp (id X) r) r := sorry

/-- Sequential composition is associative up to common refinement. -/
theorem comp_assoc_equivalent {Z W : ℕᵒᵖ ⥤ C}
    (r : Pro.SequentialHom X Y) (s : Pro.SequentialHom Y Z) (t : Pro.SequentialHom Z W) :
    Equivalent (comp (comp r s) t) (comp r (comp s t)) := sorry

/-- Common refinement is an equivalence relation on sequential presentations. -/
theorem equivalentEquivalence : _root_.Equivalence (Equivalent (X := X) (Y := Y)) := sorry

/-- The canonical setoid of sequential presentations modulo common refinement. -/
def setoid : Setoid (Pro.SequentialHom X Y) where
  r := Equivalent
  iseqv := equivalentEquivalence

/-- The quotient of sequential presentations by common refinement. -/
abbrev Quotient := _root_.Quotient (setoid (X := X) (Y := Y))

/-- Every morphism between the associated sequential
pro-objects has a representative given by a monotone reindexing and compatible level maps. -/
@[stacks 0G2W "every morphism of sequential pro-objects has a sequential representative"]
theorem toHom_surjective :
    Function.Surjective
      (toHom : Pro.SequentialHom X Y →
        ((Pro.lim (C := C) ℕᵒᵖ).obj X ⟶ (Pro.lim (C := C) ℕᵒᵖ).obj Y)) := sorry

/-- Enlarging the monotone reindexing and precomposing the level maps with transitions does not
change the represented pro-morphism. -/
theorem toHom_refine (r : Pro.SequentialHom X Y)
    (reindex' : ℕ →o ℕ) (hle : r.reindex ≤ reindex') :
    (r.refine reindex' hle).toHom = r.toHom := sorry

/-- Two monotone representatives determine the same pro-object
morphism if and only if they agree after one common monotone refinement. -/
@[stacks 0G2W "equality of sequential pro-morphism presentations"]
theorem toHom_eq_iff (r₁ r₂ : Pro.SequentialHom X Y) :
    r₁.toHom = r₂.toHom ↔ Equivalent r₁ r₂ := sorry

/-- The canonical map from common-refinement classes to morphisms of the associated pro-objects. -/
noncomputable def quotientToHom :
    Quotient (X := X) (Y := Y) →
      ((Pro.lim (C := C) ℕᵒᵖ).obj X ⟶ (Pro.lim (C := C) ℕᵒᵖ).obj Y) :=
  _root_.Quotient.lift toHom (fun r₁ r₂ h ↦ (toHom_eq_iff r₁ r₂).mpr h)

/-- The quotient-to-Pro-Hom map evaluates a representative class by its canonical pro-morphism. -/
@[simp]
theorem quotientToHom_mk (r : Pro.SequentialHom X Y) :
    quotientToHom (_root_.Quotient.mk (setoid (X := X) (Y := Y)) r) = r.toHom := sorry

/-- The canonical map from common-refinement classes to pro-morphisms is bijective. -/
@[stacks 0G2W "quotient presentation of sequential pro-morphisms"]
theorem quotientToHom_bijective :
    Function.Bijective
      (quotientToHom : Quotient (X := X) (Y := Y) →
        ((Pro.lim (C := C) ℕᵒᵖ).obj X ⟶ (Pro.lim (C := C) ℕᵒᵖ).obj Y)) := sorry

end CategoryTheory.Pro.SequentialHom
