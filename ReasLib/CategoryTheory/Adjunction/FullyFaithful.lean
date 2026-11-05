/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Full faithfulness criteria for adjunctions

This module collects cancellation through an adjunction and the standard unit/counit
characterizations of full faithfulness.
-/

@[expose] public section

universe vC uC vD uD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The counit is an isomorphism when the right adjoint has an explicit inverse on
morphisms. Its inverse is the preimage of the unit, without selecting an inverse from
an `IsIso` proof. -/
def counitIsoOfRFullyFaithful (adj : L ⊣ R) (hR : R.FullyFaithful) :
    R ⋙ L ≅ 𝟭 D :=
  NatIso.ofComponents (fun X =>
    { hom := adj.counit.app X
      inv := hR.preimage (adj.unit.app (R.obj X))
      hom_inv_id := by
        rw [← adj.counit_naturality (hR.preimage (adj.unit.app (R.obj X)))]
        simp only [hR.map_preimage]
        exact adj.left_triangle_components (R.obj X)
      inv_hom_id := by
        apply hR.map_injective
        simp only [Functor.map_comp, hR.map_preimage, Functor.map_id]
        exact adj.right_triangle_components X })
    (fun f => adj.counit.naturality f)

@[simp]
theorem counitIsoOfRFullyFaithful_hom (adj : L ⊣ R) (hR : R.FullyFaithful) :
    (adj.counitIsoOfRFullyFaithful hR).hom = adj.counit := rfl

@[simp]
theorem counitIsoOfRFullyFaithful_inv_app
    (adj : L ⊣ R) (hR : R.FullyFaithful) (X : D) :
    (adj.counitIsoOfRFullyFaithful hR).inv.app X =
      hR.preimage (adj.unit.app (R.obj X)) := rfl

namespace FullyFaithful

/-- If `L ⋙ R` is fully faithful and `L ⊣ R`, then `L` is fully faithful. -/
@[stacks 0FWV "left adjoint from a fully faithful composite"]
theorem left_of_comp
    (adj : L ⊣ R) (hcomp : Nonempty (L ⋙ R).FullyFaithful) :
    Nonempty L.FullyFaithful := sorry

/-- If `R ⋙ L` is fully faithful and `L ⊣ R`, then `R` is fully faithful. -/
@[stacks 0FWV "right adjoint from a fully faithful composite"]
theorem right_of_comp
    (adj : L ⊣ R) (hcomp : Nonempty (R ⋙ L).FullyFaithful) :
    Nonempty R.FullyFaithful := sorry

/-- A left adjoint is fully faithful exactly when the unit of the adjunction is an isomorphism. -/
@[stacks 07RB "left full faithfulness iff the unit is invertible"]
theorem left_iff_isIso_unit (adj : L ⊣ R) :
    Nonempty L.FullyFaithful ↔ IsIso adj.unit := sorry

/-- A left adjoint is fully faithful exactly when the identity is isomorphic to the
right-left composite. -/
theorem left_iff_id_iso_comp (adj : L ⊣ R) :
    Nonempty L.FullyFaithful ↔ Nonempty (𝟭 C ≅ L ⋙ R) := sorry

/-- A right adjoint is fully faithful exactly when the counit of the adjunction is an isomorphism. -/
@[stacks 07RB "right full faithfulness iff the counit is invertible"]
theorem right_iff_isIso_counit (adj : L ⊣ R) :
    Nonempty R.FullyFaithful ↔ IsIso adj.counit := sorry

/-- A right adjoint is fully faithful exactly when the left-right composite is isomorphic to
the identity. -/
theorem right_iff_comp_iso_id (adj : L ⊣ R) :
    Nonempty R.FullyFaithful ↔ Nonempty (R ⋙ L ≅ 𝟭 D) := sorry

/-- A right adjoint is fully faithful when every component of the counit is invertible. The
inverse on morphisms is exposed explicitly, so consumers do not need temporary `Full` and
`Faithful` instances. -/
noncomputable def rightOfCounitAppIsIso (adj : L ⊣ R)
    (h : ∀ X : D, IsIso (adj.counit.app X)) : R.FullyFaithful where
  preimage {X Y} f :=
    @inv _ _ _ _ (adj.counit.app X) (h X) ≫
      (adj.homEquiv (R.obj X) Y).symm f
  map_preimage := sorry
  preimage_map := sorry

/-- For an explicitly fully faithful right adjoint, an object lies in its essential image exactly
when the corresponding unit component is invertible. -/
theorem mem_essImage_iff_isIso_unit_app (adj : L ⊣ R) (hR : R.FullyFaithful) (X : C) :
    R.essImage X ↔ IsIso (adj.unit.app X) := sorry

end FullyFaithful

end CategoryTheory.Adjunction
