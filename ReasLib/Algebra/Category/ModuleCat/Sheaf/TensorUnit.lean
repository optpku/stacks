/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor units for sheaves of modules

This module owns an abstract comparison between the sheafification model of the
structure module and the tensor unit of `SheafOfModules R` for an arbitrary ring
sheaf and an externally supplied monoidal structure.  The canonical commutative
ringed-site comparison, which needs no bridge hypothesis, is owned by
`SheafOfModules.RingedSite.unitIsoTensorUnit`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{max u v}}

/-- The sheafification model of the structure module associated to an arbitrary sheaf of
rings. -/
@[stacks 03L6 "sheafification model of the structure module"]
noncomputable abbrev sheafifiedUnitModel
    (R : Sheaf J RingCat.{max u v}) : SheafOfModules R :=
  ((SheafOfModules.forget R ⋙
      PresheafOfModules.restrictScalars (𝟙 (R.obj))) ⋙
    PresheafOfModules.sheafification (𝟙 (R.obj))).obj (SheafOfModules.unit R)

/-- The counit from the sheafification model of the structure module to the structure module. -/
@[stacks 03L6 "structure-module sheafification counit"]
noncomputable abbrev sheafifiedUnitCounit :
    sheafifiedUnitModel R ⟶ SheafOfModules.unit R :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (R.obj))).counit.app (SheafOfModules.unit R)

/-- The named inverse of the counit from the sheafification model of the structure module. -/
noncomputable def sheafifiedUnitCounitInv :
    SheafOfModules.unit R ⟶ sheafifiedUnitModel R :=
  @CategoryTheory.inv _ _ _ _
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (R.obj))).counit.app (SheafOfModules.unit R))
    (NatIso.isIso_app_of_isIso
      (PresheafOfModules.sheafificationAdjunction (𝟙 (R.obj))).counit
      (SheafOfModules.unit R))

/-- The structure-module sheafification counit followed by its named inverse is the identity. -/
@[simp, stacks 03L6 "structure-module sheafification counit forward-inverse law"]
theorem sheafifiedUnitCounit_hom_inv_id :
    sheafifiedUnitCounit (R := R) ≫ sheafifiedUnitCounitInv (R := R) = 𝟙 _ := by
  unfold sheafifiedUnitCounit sheafifiedUnitCounitInv
  exact @IsIso.hom_inv_id _ _ _ _ _
    (NatIso.isIso_app_of_isIso
      (PresheafOfModules.sheafificationAdjunction (𝟙 (R.obj))).counit
      (SheafOfModules.unit R))

/-- The named inverse followed by the structure-module sheafification counit is the identity. -/
@[simp, stacks 03L6 "structure-module sheafification counit inverse-forward law"]
theorem sheafifiedUnitCounit_inv_hom_id :
    sheafifiedUnitCounitInv (R := R) ≫ sheafifiedUnitCounit (R := R) = 𝟙 _ := by
  unfold sheafifiedUnitCounit sheafifiedUnitCounitInv
  exact @IsIso.inv_hom_id _ _ _ _ _
    (NatIso.isIso_app_of_isIso
      (PresheafOfModules.sheafificationAdjunction (𝟙 (R.obj))).counit
      (SheafOfModules.unit R))

/-- The structure-module sheafification counit as a literal isomorphism with a named inverse. -/
@[stacks 03L6 "structure-module sheafification counit isomorphism"]
noncomputable def sheafifiedUnitCounitIso :
    sheafifiedUnitModel R ≅ SheafOfModules.unit R where
  hom := sheafifiedUnitCounit (R := R)
  inv := sheafifiedUnitCounitInv (R := R)
  hom_inv_id := sheafifiedUnitCounit_hom_inv_id (R := R)
  inv_hom_id := sheafifiedUnitCounit_inv_hom_id (R := R)

/-- The forward map of `sheafifiedUnitCounitIso` is the sheafification counit. -/
@[simp, stacks 03L6 "structure-module sheafification counit isomorphism hom"]
theorem sheafifiedUnitCounitIso_hom :
    (sheafifiedUnitCounitIso (R := R)).hom = sheafifiedUnitCounit (R := R) := rfl

/-- The inverse map of `sheafifiedUnitCounitIso` is the named counit inverse. -/
@[simp, stacks 03L6 "structure-module sheafification counit isomorphism inverse"]
theorem sheafifiedUnitCounitIso_inv :
    (sheafifiedUnitCounitIso (R := R)).inv = sheafifiedUnitCounitInv (R := R) := rfl

variable [MonoidalCategory (SheafOfModules R)]

/-- An abstract bridge identifying the ambient tensor unit with the sheafification model of the
structure module.  It is retained for genuinely arbitrary ring sheaves and caller-chosen
monoidal structures; canonical commutative ringed sites do not require this class. -/
class UnitIsSheafifiedUnit (R : Sheaf J RingCat.{max u v})
    [MonoidalCategory (SheafOfModules R)] : Prop where
  eq : sheafifiedUnitModel R = 𝟙_ (SheafOfModules R)

/-- The equality supplied by `UnitIsSheafifiedUnit`, exposed independently of its class field. -/
@[stacks 03L6 "sheafified structure module is the abstract tensor unit"]
theorem sheafifiedUnitModel_eq_tensorUnit [UnitIsSheafifiedUnit R] :
    sheafifiedUnitModel R = 𝟙_ (SheafOfModules R) :=
  UnitIsSheafifiedUnit.eq (R := R)

/-- Compatibility bridge for the former name of `sheafifiedUnitModel_eq_tensorUnit`. -/
theorem tensorUnit_eq_sheafification_unit_model [UnitIsSheafifiedUnit R] :
    sheafifiedUnitModel R = 𝟙_ (SheafOfModules R) :=
  sheafifiedUnitModel_eq_tensorUnit (R := R)

/-- The explicit morphism from the structure module to the ambient tensor unit. -/
@[stacks 03L6 "structure module to abstract tensor unit"]
noncomputable def unitToTensorUnit [UnitIsSheafifiedUnit R] :
    SheafOfModules.unit R ⟶ 𝟙_ (SheafOfModules R) :=
  sheafifiedUnitCounitInv (R := R) ≫
    (eqToIso (UnitIsSheafifiedUnit.eq (R := R))).hom

/-- The explicit morphism from the ambient tensor unit to the structure module. -/
@[stacks 03L6 "abstract tensor unit to structure module"]
noncomputable def tensorUnitToUnit [UnitIsSheafifiedUnit R] :
    𝟙_ (SheafOfModules R) ⟶ SheafOfModules.unit R :=
  (eqToIso (UnitIsSheafifiedUnit.eq (R := R))).inv ≫
    sheafifiedUnitCounit (R := R)

/-- The structure-module comparison followed by its reverse is the identity. -/
@[simp, stacks 03L6 "abstract tensor-unit comparison forward-inverse law"]
theorem unitToTensorUnit_comp_tensorUnitToUnit [UnitIsSheafifiedUnit R] :
    unitToTensorUnit (R := R) ≫ tensorUnitToUnit (R := R) = 𝟙 _ :=
  ((sheafifiedUnitCounitIso (R := R)).symm ≪≫
    eqToIso (UnitIsSheafifiedUnit.eq (R := R))).hom_inv_id

/-- The reverse comparison followed by the structure-module comparison is the identity. -/
@[simp, stacks 03L6 "abstract tensor-unit comparison inverse-forward law"]
theorem tensorUnitToUnit_comp_unitToTensorUnit [UnitIsSheafifiedUnit R] :
    tensorUnitToUnit (R := R) ≫ unitToTensorUnit (R := R) = 𝟙 _ :=
  ((sheafifiedUnitCounitIso (R := R)).symm ≪≫
    eqToIso (UnitIsSheafifiedUnit.eq (R := R))).inv_hom_id

/-- The canonical isomorphism from the structure module to the ambient tensor unit, built
literally from the named comparison maps. -/
@[stacks 03L6 "abstract tensor-unit comparison isomorphism"]
noncomputable def unitIsoTensorUnit [UnitIsSheafifiedUnit R] :
    SheafOfModules.unit R ≅ 𝟙_ (SheafOfModules R) where
  hom := unitToTensorUnit (R := R)
  inv := tensorUnitToUnit (R := R)
  hom_inv_id := unitToTensorUnit_comp_tensorUnitToUnit (R := R)
  inv_hom_id := tensorUnitToUnit_comp_unitToTensorUnit (R := R)

/-- The forward map of `unitIsoTensorUnit` is the named structure-module comparison. -/
@[simp, stacks 03L6 "abstract tensor-unit comparison isomorphism hom"]
theorem unitIsoTensorUnit_hom [UnitIsSheafifiedUnit R] :
    (unitIsoTensorUnit (R := R)).hom = unitToTensorUnit (R := R) := rfl

/-- The inverse map of `unitIsoTensorUnit` is the named reverse comparison. -/
@[simp, stacks 03L6 "abstract tensor-unit comparison isomorphism inverse"]
theorem unitIsoTensorUnit_inv [UnitIsSheafifiedUnit R] :
    (unitIsoTensorUnit (R := R)).inv = tensorUnitToUnit (R := R) := rfl



end SheafOfModules
