/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ResidueField.PointFactor
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.SelectedResidue

/-!
# A pullback point from the right canonical residue-field isomorphism

The original map `Spec κ(x) ⟶ S` and the inverse of the given canonical
residue-field map at `y` supply the homomorphism used by `SelectedResidue`.
All point transports in the factorization use the base point `g y`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Pullback.RightResidueFieldPoint

variable {X Y S : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) (hxy : f x = g y)
  [IsIso (g.residueFieldMap y)]

/-- The original field-valued point of the base scheme. -/
def baseMap : Spec (X.residueField x) ⟶ S :=
  X.fromSpecResidueField x ≫ f

/-- Compatibility places the original field-valued point over `g y`. -/
theorem baseMap_apply (h : f x = g y) : baseMap f x default = g y := by
  change (X.fromSpecResidueField x ≫ f) default = g y
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  exact h

/-- The inverse of the given canonical residue-field isomorphism on the right. -/
def rightResidueEquiv : Y.residueField y ≃+* S.residueField (g y) :=
  (asIso (g.residueFieldMap y)).symm.commRingCatIsoToRingEquiv

/-- The inverse equivalence is exactly the given canonical residue map. -/
@[simp]
theorem rightResidueEquiv_symm_toRingHom :
    (rightResidueEquiv g y).symm.toRingHom = (g.residueFieldMap y).hom := rfl

/-- The actual homomorphism extracted from the original map and the right inverse. -/
def residueHom : Y.residueField y →+* X.residueField x :=
  SpecFieldPointFactor.liftResidueHom (baseMap f x) (g y)
    (baseMap_apply f g x y hxy) y (rightResidueEquiv g y)

/-- The extracted homomorphism gives the square required by `SelectedResidue`. -/
theorem residueHom_square :
    (Spec.map (CommRingCat.ofHom (residueHom f g x y hxy)) ≫
      Y.fromSpecResidueField y) ≫ g = X.fromSpecResidueField x ≫ f := by
  change SpecFieldPointFactor.lift (baseMap f x) (g y)
    (baseMap_apply f g x y hxy) y (rightResidueEquiv g y) ≫ g = baseMap f x
  apply SpecFieldPointFactor.lift_comp _ _ _ _ _ _ rfl
  simpa using rightResidueEquiv_symm_toRingHom g y

/-- The field-valued lift, reusing the selected-residue construction. -/
def lift : Spec (X.residueField x) ⟶ pullback f g :=
  SelectedResidue.lift f g x y (residueHom f g x y hxy)
    (residueHom_square f g x y hxy)

/-- The lift has the original first component. -/
@[simp]
theorem lift_fst : lift f g x y hxy ≫ pullback.fst f g = X.fromSpecResidueField x :=
  SelectedResidue.lift_fst f g x y (residueHom f g x y hxy)
    (residueHom_square f g x y hxy)

/-- The lift has the component determined by the extracted residue homomorphism. -/
@[simp]
theorem lift_snd : lift f g x y hxy ≫ pullback.snd f g =
    Spec.map (CommRingCat.ofHom (residueHom f g x y hxy)) ≫
      Y.fromSpecResidueField y :=
  SelectedResidue.lift_snd f g x y (residueHom f g x y hxy)
    (residueHom_square f g x y hxy)

/-- The actual pullback point supplied by the right canonical residue isomorphism. -/
def point : (pullback f g : Scheme) :=
  SelectedResidue.point f g x y (residueHom f g x y hxy)
    (residueHom_square f g x y hxy)

/-- The first projection of the supplied point is `x`. -/
@[simp]
theorem point_fst : pullback.fst f g (point f g x y hxy) = x :=
  SelectedResidue.point_fst f g x y (residueHom f g x y hxy)
    (residueHom_square f g x y hxy)

/-- The second projection of the supplied point is `y`. -/
@[simp]
theorem point_snd : pullback.snd f g (point f g x y hxy) = y :=
  SelectedResidue.point_snd f g x y (residueHom f g x y hxy)
    (residueHom_square f g x y hxy)

/-- The selected-residue equivalence, with its original forward and inverse maps. -/
def residueEquiv : (pullback f g).residueField (point f g x y hxy) ≃+*
    X.residueField x :=
  SelectedResidue.residueEquiv f g x y (residueHom f g x y hxy)
    (residueHom_square f g x y hxy)

/-- The inverse is the canonical first-projection residue map with its point transport. -/
@[simp]
theorem residueEquiv_symm_toRingHom :
    (residueEquiv f g x y hxy).symm.toRingHom =
      ((X.residueFieldCongr (point_fst f g x y hxy)).inv ≫
        (pullback.fst f g).residueFieldMap (point f g x y hxy)).hom :=
  SelectedResidue.residueEquiv_symm_toRingHom f g x y (residueHom f g x y hxy)
    (residueHom_square f g x y hxy)

/-- The canonical second-projection residue map at the supplied point. -/
def canonicalMap : Y.residueField y →+*
    (pullback f g).residueField (point f g x y hxy) :=
  SelectedResidue.canonicalMap f g x y (residueHom f g x y hxy)
    (residueHom_square f g x y hxy)

/-- The residue equivalence sends the second canonical map to the extracted homomorphism. -/
theorem canonical_map_commutes :
    (residueEquiv f g x y hxy).toRingHom.comp (canonicalMap f g x y hxy) =
      residueHom f g x y hxy :=
  SelectedResidue.canonical_map_commutes f g x y (residueHom f g x y hxy)
    (residueHom_square f g x y hxy)

end AlgebraicGeometry.Scheme.Pullback.RightResidueFieldPoint
