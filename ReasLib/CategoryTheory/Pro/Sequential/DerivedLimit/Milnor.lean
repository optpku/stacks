module

public import ReasLib.CategoryTheory.InverseSystem.Milnor
public import ReasLib.CategoryTheory.Pro.Sequential.Presentation

/-!
# Milnor product squares from sequential representatives

The level maps of a monotone sequential representative assemble into the two product maps of the
Milnor square.  This layer uses only preadditivity and countable products; cokernels enter only in
the separate first-derived-limit leaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.Pro.SequentialHom

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : SequentialInverseSystem C}
variable [HasCountableProducts C]

/-- The first product map of a sequential representative, formed from its level maps. -/
noncomputable def firstProductMap (r : Pro.SequentialHom X Y) :
    (∏ᶜ X.family) ⟶ ∏ᶜ Y.family :=
  Pi.lift fun n ↦ Pi.π X.family (r.reindex n) ≫ r.hom.app (op n)

/-- The component of the telescoping second product map at target stage `n`. -/
noncomputable def secondProductComponent (r : Pro.SequentialHom X Y) (n : ℕ) :
    (∏ᶜ X.family) ⟶ Y.obj (op n) :=
  Finset.sum (Finset.range (r.reindex (n + 1) - r.reindex n)) fun k ↦
    Pi.π X.family (r.reindex n + k) ≫
      X.transitionMap (Nat.le_add_right (r.reindex n) k) ≫ r.hom.app (op n)

/-- The second product map of a sequential representative, assembled from its telescoping
components. -/
noncomputable def secondProductMap (r : Pro.SequentialHom X Y) :
    (∏ᶜ X.family) ⟶ ∏ᶜ Y.family :=
  Pi.lift fun n ↦ r.secondProductComponent n

/-- The first product map is computed by the corresponding product projection. -/
theorem firstProductMap_comp_π (r : Pro.SequentialHom X Y) (n : ℕ) :
    r.firstProductMap ≫ Pi.π Y.family n =
      Pi.π X.family (r.reindex n) ≫ r.hom.app (op n) := sorry

/-- The second product map is computed by its telescoping component. -/
theorem secondProductMap_comp_π (r : Pro.SequentialHom X Y) (n : ℕ) :
    r.secondProductMap ≫ Pi.π Y.family n = r.secondProductComponent n := sorry

/-- The two product maps form the canonical Milnor square with the difference endomorphisms. -/
theorem milnorDifferenceCommSq (r : Pro.SequentialHom X Y) :
    CommSq X.milnorDifferenceMap r.firstProductMap r.secondProductMap
      Y.milnorDifferenceMap := sorry

end CategoryTheory.Pro.SequentialHom
