module

public import ReasLib.CategoryTheory.Adjunction.IsomorphismProperty
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restrictions of an adjunction to its isomorphism loci

The unit and counit isomorphism loci are preserved by the opposite adjoint.  This
file turns those two preservation facts into the canonical full-subcategory
restrictions, using the generic object-property restriction API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe vC vD uC uD

namespace CategoryTheory.Adjunction

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- The full subcategory on which the unit of `adj` is invertible. -/
@[stacks 0D7Q "unit-isomorphism subcategory"]
abbrev unitIsoSubcategory := adj.unitIsoProperty.FullSubcategory

/-- The full subcategory on which the counit of `adj` is invertible. -/
@[stacks 0D7R "counit-isomorphism subcategory"]
abbrev counitIsoSubcategory := adj.counitIsoProperty.FullSubcategory

/-- The counit is invertible at the image of every unit-isomorphism object. -/
@[stacks 0D7Q "counit isomorphism on the unit locus", stacks 0D7R]
theorem counitIso_of_unitIso (X : adj.unitIsoSubcategory) :
    adj.counitIsoProperty (F.obj X.obj) := sorry

/-- The unit is invertible at the image of every counit-isomorphism object. -/
@[stacks 0D7Q "unit isomorphism on the counit locus", stacks 0D7R]
theorem unitIso_of_counitIso (Y : adj.counitIsoSubcategory) :
    adj.unitIsoProperty (G.obj Y.obj) := sorry

/-- The left adjoint carries the unit-isomorphism locus into the counit-isomorphism locus. -/
@[stacks 0D7Q "left adjoint preserves the unit-isomorphism locus"]
theorem unitIsoProperty_le_counitIsoProperty_inverseImage :
    adj.unitIsoProperty ≤ adj.counitIsoProperty.inverseImage F := sorry

/-- The right adjoint carries the counit-isomorphism locus into the unit-isomorphism locus. -/
@[stacks 0D7Q "right adjoint preserves the counit-isomorphism locus", stacks 0D7R]
theorem counitIsoProperty_le_unitIsoProperty_inverseImage :
    adj.counitIsoProperty ≤ adj.unitIsoProperty.inverseImage G := sorry

/-- The left adjoint restricted to the unit-isomorphism and counit-isomorphism loci. -/
@[stacks 0D7Q "restricted left adjoint"]
noncomputable abbrev leftRestriction :
    adj.unitIsoSubcategory ⥤ adj.counitIsoSubcategory :=
  ObjectProperty.FullSubcategory.restrict F
    (unitIsoProperty_le_counitIsoProperty_inverseImage adj)

/-- The right adjoint restricted to the counit-isomorphism and unit-isomorphism loci. -/
@[stacks 0D7R "restricted right adjoint"]
noncomputable abbrev rightRestriction :
    adj.counitIsoSubcategory ⥤ adj.unitIsoSubcategory :=
  ObjectProperty.FullSubcategory.restrict G
    (counitIsoProperty_le_unitIsoProperty_inverseImage adj)

/-- The original adjunction restricts canonically to the two isomorphism loci. -/
@[stacks 0D7R "restricted adjunction"]
noncomputable abbrev restrictedAdjunction :
    adj.leftRestriction ⊣ adj.rightRestriction :=
  ObjectProperty.FullSubcategory.adjunction F G adj
    (unitIsoProperty_le_counitIsoProperty_inverseImage adj)
    (counitIsoProperty_le_unitIsoProperty_inverseImage adj)

/-- The ambient left adjoint with source restricted to the unit-isomorphism locus. -/
@[stacks 0D7Q "left adjoint on the unit locus"]
noncomputable abbrev leftAdjoint : adj.unitIsoSubcategory ⥤ D :=
  adj.leftRestriction ⋙ adj.counitIsoProperty.ι

/-- The ambient right adjoint with source restricted to the counit-isomorphism locus. -/
@[stacks 0D7R "right adjoint on the counit locus"]
noncomputable abbrev rightAdjoint : adj.counitIsoSubcategory ⥤ C :=
  adj.rightRestriction ⋙ adj.unitIsoProperty.ι

/-- The inverse of the unit at an object in the unit-isomorphism locus. -/
@[stacks 0D7Q "unit inverse"]
noncomputable def unitInv (X : adj.unitIsoSubcategory) :
    G.obj (F.obj X.obj) ⟶ X.obj :=
  @inv _ _ _ _ (adj.unit.app X.obj) X.property

/-- The inverse of the counit at an object in the counit-isomorphism locus. -/
@[stacks 0D7R "counit inverse"]
noncomputable def counitInv (Y : adj.counitIsoSubcategory) :
    Y.obj ⟶ F.obj (G.obj Y.obj) :=
  @inv _ _ _ _ (adj.counit.app Y.obj) Y.property

/- The four equations below are the stable downstream interface for the explicit inverses. -/
/-- The unit followed by its inverse is the identity on the unit-locus object. -/
@[stacks 0D7Q, simp]
theorem unit_comp_unitInv (X : adj.unitIsoSubcategory) :
    adj.unit.app X.obj ≫ adj.unitInv X = 𝟙 X.obj := sorry

/-- The inverse of the unit followed by the unit is the identity on `G.obj (F.obj X)`. -/
@[stacks 0D7Q, simp]
theorem unitInv_comp_unit (X : adj.unitIsoSubcategory) :
    adj.unitInv X ≫ adj.unit.app X.obj = 𝟙 (G.obj (F.obj X.obj)) := sorry

/-- The counit followed by its inverse is the identity on `F.obj (G.obj Y)`. -/
@[stacks 0D7R, simp]
theorem counit_comp_counitInv (Y : adj.counitIsoSubcategory) :
    adj.counit.app Y.obj ≫ adj.counitInv Y = 𝟙 (F.obj (G.obj Y.obj)) := sorry

/-- The inverse of the counit followed by the counit is the identity on the counit-locus object. -/
@[stacks 0D7R, simp]
theorem counitInv_comp_counit (Y : adj.counitIsoSubcategory) :
    adj.counitInv Y ≫ adj.counit.app Y.obj = 𝟙 Y.obj := sorry

/-- The restricted left adjoint is fully faithful. -/
@[stacks 0D7Q "restricted left adjoint is fully faithful"]
noncomputable def leftRestriction_fullyFaithful :
    adj.leftRestriction.FullyFaithful :=
  { preimage := fun {X Y} f ↦
      ObjectProperty.homMk
        (adj.homEquiv X.obj (F.obj Y.obj) f.hom ≫ adj.unitInv Y)
    map_preimage := sorry
    preimage_map := sorry }

/-- The restricted right adjoint is fully faithful. -/
@[stacks 0D7Q "restricted right adjoint is fully faithful", stacks 0D7R]
noncomputable def rightRestriction_fullyFaithful :
    adj.rightRestriction.FullyFaithful :=
  { preimage := fun {X Y} f ↦
      ObjectProperty.homMk
        (adj.counitInv X ≫ (adj.homEquiv (G.obj X.obj) Y.obj).symm f.hom)
    map_preimage := sorry
    preimage_map := sorry }

/-- The ambient left adjoint restricted to the unit locus is fully faithful. -/
@[stacks 0D7Q "left adjoint on the unit locus is fully faithful"]
noncomputable def leftAdjoint_fullyFaithful :
    adj.leftAdjoint.FullyFaithful :=
  (adj.leftRestriction_fullyFaithful).comp adj.counitIsoProperty.fullyFaithfulι

/-- The ambient right adjoint restricted to the counit locus is fully faithful. -/
@[stacks 0D7Q "right adjoint on the counit locus is fully faithful", stacks 0D7R]
noncomputable def rightAdjoint_fullyFaithful :
    adj.rightAdjoint.FullyFaithful :=
  (adj.rightRestriction_fullyFaithful).comp adj.unitIsoProperty.fullyFaithfulι

/-- The restricted left adjoint induces bijections on hom-sets. -/
@[stacks 0D7Q "hom bijection for the restricted left adjoint"]
theorem leftAdjoint_map_bijective (X Y : adj.unitIsoSubcategory) :
    Function.Bijective
      (adj.leftAdjoint.map : (X ⟶ Y) → (F.obj X.obj ⟶ F.obj Y.obj)) := sorry

/-- The restricted right adjoint induces bijections on hom-sets. -/
@[stacks 0D7Q "hom bijection for the restricted right adjoint", stacks 0D7R]
theorem rightAdjoint_map_bijective (X Y : adj.counitIsoSubcategory) :
    Function.Bijective
      (adj.rightAdjoint.map : (X ⟶ Y) → (G.obj X.obj ⟶ G.obj Y.obj)) := sorry

/- `leftRestriction_fullyFaithful` and `rightRestriction_fullyFaithful` have explicit concrete
   `preimage` fields.  Their remaining `sorryAx` dependencies, shown below, are confined to the
   Prop-valued `map_preimage` and `preimage_map` laws. -/

end CategoryTheory.Adjunction

end
