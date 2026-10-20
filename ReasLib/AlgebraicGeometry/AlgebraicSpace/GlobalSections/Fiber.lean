module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.OverField

/-! # Global sections of field-valued fibres -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Every field-valued fibre has global sections given bijectively by its base field
through the canonical ring map. -/
def fiberGlobalSectionsBijective {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ p : FieldValuedPoint Y, Function.Bijective (globalSectionsMap (fiberOverField f p))

/-- Fibrewise global-sections bijectivity is bijectivity of the canonical ring map
for every field-valued point of the target. -/
theorem fiberGlobalSectionsBijective_iff {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    fiberGlobalSectionsBijective f ↔
      ∀ p : FieldValuedPoint Y, Function.Bijective (globalSectionsMap (fiberOverField f p)) := sorry

end AlgebraicGeometry.AlgebraicSpace
