module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive.Section

/-!
# Stalk powers of module sections

This file defines the morphisms representing powers of a module section and their values in
stalks.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The morphism from the tensor unit representing the `n`th power of a module section in its
reflexive tensor-power sequence. -/
noncomputable def rankOneReflexiveSectionPowerMorphism {ℱ : X.Modules}
    (s : 𝟙_ X.Modules ⟶ ℱ) :
    ∀ n : ℕ, 𝟙_ X.Modules ⟶ rankOneReflexiveSectionPower ℱ n
  | 0 => 𝟙 _
  | n + 1 =>
      rankOneReflexiveSectionPowerMorphism s n ≫ rankOneReflexiveSectionPowerMap s n

/-- The value in the stalk at `x` of the morphism representing the `n`th power of a module
section. -/
noncomputable def rankOneReflexiveSectionPowerStalkElement {ℱ : X.Modules}
    (s : 𝟙_ X.Modules ⟶ ℱ) (n : ℕ) (x : X) :
    ((TopCat.Presheaf.stalk
      (rankOneReflexiveSectionPower ℱ n).val.presheaf x : AddCommGrpCat) : Type u) :=
  RingedSpace.moduleStalkMap x
    ((RingedSpace.unitIsoTensorUnit X.toRingedSpace :
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) ≅ 𝟙_ X.Modules).hom ≫
        rankOneReflexiveSectionPowerMorphism s n)
    ((RingedSpace.unitStalkLinearEquiv x).symm (1 : X.presheaf.stalk x))

/-- The successor stalk power is the image of the previous stalk power under the stalk map of
multiplication by the original section. -/
theorem rankOneReflexiveSectionPowerStalkElement_succ {ℱ : X.Modules}
    (s : 𝟙_ X.Modules ⟶ ℱ) (n : ℕ) (x : X) :
    rankOneReflexiveSectionPowerStalkElement s (n + 1) x =
      RingedSpace.moduleStalkMap x (rankOneReflexiveSectionPowerMap s n)
        (rankOneReflexiveSectionPowerStalkElement s n x) := sorry

end AlgebraicGeometry.Scheme.Modules
