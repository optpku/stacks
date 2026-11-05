/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stalk

/-!
# Stalks at distinguished points of fibres

This leaf owns the local rings and canonical maps attached to the point of a
scheme-theoretic fibre determined by a point of the source.  It is independent
of tangent- and cotangent-space constructions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The local ring of the scheme-theoretic fibre `X_{f(x)}` at the point
`f.asFiber x` determined by `x`. -/
abbrev fiberStalkAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : CommRingCat :=
  (f.fiber (f x)).presheaf.stalk (f.asFiber x)

/-- The residue field of the distinguished fibre point `f.asFiber x`. -/
abbrev fiberResidueFieldAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : CommRingCat :=
  (f.fiber (f x)).residueField (f.asFiber x)

/-- The map from `κ(f(x))` to the stalk of the fibre at its distinguished
point, induced by the morphism from that fibre to `Spec κ(f(x))`. -/
noncomputable def fiberBaseResidueFieldToStalk
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    S.residueField (f x) ⟶ fiberStalkAt f x := by
  let e :
      (Spec (S.residueField (f x))).presheaf.stalk
          (IsLocalRing.closedPoint (S.residueField (f x))) ⟶
        (Spec (S.residueField (f x))).presheaf.stalk
          ((f.fiberToSpecResidueField (f x)) (f.asFiber x)) :=
    ((Spec (S.residueField (f x))).presheaf.stalkCongr
      (.of_eq (Scheme.Hom.fiberToSpecResidueField_apply f (f x) (f.asFiber x)).symm)).hom
  let phi1 :
      S.residueField (f x) ⟶
        (Spec (S.residueField (f x))).presheaf.stalk
          (IsLocalRing.closedPoint (S.residueField (f x))) :=
    (AlgebraicGeometry.stalkClosedPointIso (S.residueField (f x))).inv
  let phi2 :
      S.residueField (f x) ⟶
        (Spec (S.residueField (f x))).presheaf.stalk
          ((f.fiberToSpecResidueField (f x)) (f.asFiber x)) :=
    phi1 ≫ e
  exact phi2 ≫ (f.fiberToSpecResidueField (f x)).stalkMap (f.asFiber x)

/-- The point `f.asFiberHom x : Spec κ(x) ⟶ X_{f(x)}` induces a morphism
from the stalk of the fibre to the source residue field `κ(x)`. -/
noncomputable def fiberStalkToSourceResidueField
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fiberStalkAt f x ⟶ X.residueField x := by
  let e :
      fiberStalkAt f x ⟶
        (f.fiber (f x)).presheaf.stalk
          ((f.asFiberHom x) (IsLocalRing.closedPoint (X.residueField x))) :=
    ((f.fiber (f x)).presheaf.stalkCongr (.of_eq (by simp))).inv
  exact e ≫ Scheme.stalkClosedPointTo (f.asFiberHom x)

/-- The fibre inclusion induces a morphism from the source stalk at `x` to
the stalk of the fibre at its distinguished point. -/
noncomputable def sourceStalkToFiberStalk
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    X.presheaf.stalk x ⟶ fiberStalkAt f x :=
  let e : X.presheaf.stalk x ⟶ X.presheaf.stalk ((f.fiberι (f x)) (f.asFiber x)) :=
    ((X.presheaf.stalkCongr (.of_eq (by simp))).inv)
  e ≫ (f.fiberι (f x)).stalkMap (f.asFiber x)

/-- The fibre-inclusion stalk map represents the canonical map from its stalk spectrum. -/
theorem SpecMap_sourceStalkToFiberStalk_fromSpecStalk
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Spec.map (sourceStalkToFiberStalk f x) ≫ X.fromSpecStalk x =
      (f.fiber (f x)).fromSpecStalk (f.asFiber x) ≫ f.fiberι (f x) := by
  simp [sourceStalkToFiberStalk, Spec.map_comp, Category.assoc,
    TopCat.Presheaf.stalkCongr]

/-- The base-field action on the fibre stalk represents the structure morphism. -/
theorem SpecMap_fiberBaseResidueFieldToStalk
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Spec.map (fiberBaseResidueFieldToStalk f x) =
      (f.fiber (f x)).fromSpecStalk (f.asFiber x) ≫
        f.fiberToSpecResidueField (f x) := by
  simp [fiberBaseResidueFieldToStalk, Spec.map_comp, Category.assoc,
    Spec_stalkClosedPointIso, TopCat.Presheaf.stalkCongr]

/-- The residue map of the base point and the fibre inclusion form the
canonical square on stalks at the distinguished point of the fibre. -/
theorem fiberBaseResidueFieldToStalk_fac
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    S.residue (f x) ≫ fiberBaseResidueFieldToStalk f x =
      f.stalkMap x ≫ sourceStalkToFiberStalk f x := by
  apply Spec.map_injective
  apply (cancel_mono (S.fromSpecStalk (f x))).1
  simp only [Spec.map_comp, Category.assoc]
  change Spec.map (fiberBaseResidueFieldToStalk f x) ≫
      S.fromSpecResidueField (f x) = _
  rw [SpecMap_fiberBaseResidueFieldToStalk, Category.assoc, ← f.fiber_fac,
    ← Category.assoc, ← SpecMap_sourceStalkToFiberStalk_fromSpecStalk,
    Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- The base residue field `κ(f(x))` acts on the stalk of the fibre. -/
noncomputable instance fiberStalkBaseResidueFieldAlgebra
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Algebra (S.residueField (f x)) (fiberStalkAt f x) :=
  (fiberBaseResidueFieldToStalk f x).hom.toAlgebra

/-- The residue field of the distinguished fibre point is an algebra over its
local ring through the ordinary residue morphism. -/
noncomputable instance fiberStalkFiberResidueFieldAlgebra
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Algebra (fiberStalkAt f x) (fiberResidueFieldAt f x) :=
  ((f.fiber (f x)).residue (f.asFiber x)).hom.toAlgebra

/-- The `κ(f(x))`-action on the residue field of the distinguished fibre
point factors through its local ring. -/
instance fiberStalkFiberResidueFieldIsScalarTower
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsScalarTower (S.residueField (f x)) (fiberStalkAt f x) (fiberResidueFieldAt f x) := by
  apply IsScalarTower.of_algebraMap_eq'
  have h : CommRingCat.ofHom
      (algebraMap (S.residueField (f x)) (fiberResidueFieldAt f x)) =
      fiberBaseResidueFieldToStalk f x ≫ (f.fiber (f x)).residue (f.asFiber x) := by
    change CommRingCat.ofHom
      (algebraMap (S.residueField (f x))
        ((f.fiberToSpecResidueField (f x)) (f.asFiber x)).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso _ _).inv ≫
        (f.fiberToSpecResidueField (f x)).residueFieldMap (f.asFiber x) = _
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc,
      Scheme.residue_residueFieldMap]
    have hphi : (stalkClosedPointIso (S.residueField (f x))).inv ≫
        ((Spec (S.residueField (f x))).presheaf.stalkCongr
          (.of_eq (Scheme.Hom.fiberToSpecResidueField_apply f (f x)
            (f.asFiber x)).symm)).hom =
        (Scheme.ΓSpecIso (S.residueField (f x))).inv ≫
          (Spec (S.residueField (f x))).presheaf.germ ⊤
            ((f.fiberToSpecResidueField (f x)) (f.asFiber x)) trivial := by
      apply (cancel_epi (Scheme.ΓSpecIso (S.residueField (f x))).hom).1
      simp [← Category.assoc, ΓSpecIso_hom_stalkClosedPointIso_inv,
        TopCat.Presheaf.stalkCongr]
    simpa only [fiberBaseResidueFieldToStalk, ← Category.assoc, hphi] using
      (Category.assoc
        ((Scheme.ΓSpecIso (S.residueField (f x))).inv ≫
          (Spec (S.residueField (f x))).presheaf.germ ⊤
            ((f.fiberToSpecResidueField (f x)) (f.asFiber x)) trivial)
        ((f.fiberToSpecResidueField (f x)).stalkMap (f.asFiber x))
        ((f.fiber (f x)).residue (f.asFiber x))).symm
  exact congrArg CommRingCat.Hom.hom h

/-- The stalk of the fibre acts on the source residue field through the
distinguished fibre point. -/
noncomputable instance fiberStalkSourceResidueFieldAlgebra
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Algebra (fiberStalkAt f x) (X.residueField x) :=
  (fiberStalkToSourceResidueField f x).hom.toAlgebra

/-- The action of `κ(f(x))` on `κ(x)` factors through the stalk of the fibre
at its distinguished point. -/
instance fiberStalkSourceResidueFieldIsScalarTower
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsScalarTower (S.residueField (f x)) (fiberStalkAt f x) (X.residueField x) := by
  apply IsScalarTower.of_algebraMap_eq'
  have h : Spec.map (fiberStalkToSourceResidueField f x) ≫
      (f.fiber (f x)).fromSpecStalk (f.asFiber x) = f.asFiberHom x := by
    dsimp [fiberStalkToSourceResidueField]
    simp only [Spec.map_comp, Category.assoc,
      TopCat.Presheaf.stalkCongr_inv,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk _
  have hh : fiberBaseResidueFieldToStalk f x ≫ fiberStalkToSourceResidueField f x =
      f.residueFieldMap x := by
    apply Spec.map_injective
    rw [Spec.map_comp, SpecMap_fiberBaseResidueFieldToStalk,
      ← Category.assoc, h, f.asFiberHom_fiberToSpecResidueField]
  exact (congrArg CommRingCat.Hom.hom hh).symm

/-- The source stalk acts on the stalk of the fibre through the fibre
inclusion. -/
noncomputable instance fiberStalkSourceStalkAlgebra
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Algebra (X.presheaf.stalk x) (fiberStalkAt f x) :=
  (sourceStalkToFiberStalk f x).hom.toAlgebra

/-- The canonical map from the distinguished fibre stalk to the source
residue field is a local ring homomorphism. -/
theorem fiberStalkToSourceResidueField_isLocalHom
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsLocalHom (fiberStalkToSourceResidueField f x).hom := by
  dsimp [fiberStalkToSourceResidueField]
  infer_instance

/-- The local map from the distinguished fibre stalk to `κ(x)` induces a
map from the residue field of the fibre point to `κ(x)`. -/
noncomputable def fiberResidueFieldToSourceResidueField
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fiberResidueFieldAt f x ⟶ X.residueField x :=
  CommRingCat.ofHom <|
    @IsLocalRing.ResidueField.lift
      (fiberStalkAt f x)
      (X.residueField x)
      inferInstance
      inferInstance
      inferInstance
      (fiberStalkToSourceResidueField f x).hom
      (fiberStalkToSourceResidueField_isLocalHom f x)

/-- The map from the distinguished fibre residue field to `κ(x)` is the
unique factorization of the fibre-stalk residue map. -/
theorem fiberStalkToSourceResidueField_factor
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    (f.fiber (f x)).residue (f.asFiber x) ≫
        fiberResidueFieldToSourceResidueField f x =
      fiberStalkToSourceResidueField f x := by
  ext a
  rfl

/-- The source residue field is an algebra over the distinguished fibre
residue field through the induced residue-field map. -/
noncomputable instance fiberResidueFieldSourceResidueFieldAlgebra
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Algebra (fiberResidueFieldAt f x) (X.residueField x) :=
  (fiberResidueFieldToSourceResidueField f x).hom.toAlgebra

/-- The action of the distinguished fibre stalk on `κ(x)` factors through
the residue field of the fibre point. -/
instance fiberResidueFieldSourceResidueFieldIsScalarTower
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsScalarTower (fiberStalkAt f x) (fiberResidueFieldAt f x)
      (X.residueField x) := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (congrArg CommRingCat.Hom.hom
    (fiberStalkToSourceResidueField_factor f x)).symm

private theorem descResidueField_stalkClosedPointTo_congr
    {K : Type u} [Field K] {Y : Scheme.{u}} (g : Spec (.of K) ⟶ Y)
    (y : Y) (h : g (IsLocalRing.closedPoint K) = y) :
    let φ := (Y.presheaf.stalkCongr (.of_eq h)).inv ≫ Scheme.stalkClosedPointTo g
    letI : IsLocalHom φ.hom := by dsimp [φ]; infer_instance
    Spec.map (Y.descResidueField φ) ≫ Y.fromSpecResidueField y = g := by
  subst y
  simpa using Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y g

set_option backward.isDefEq.respectTransparency false in
/-- The residue-field comparison represents the distinguished field-valued
point of the fibre. -/
theorem fiberResidueFieldToSourceResidueField_fromSpec
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Spec.map (fiberResidueFieldToSourceResidueField f x) ≫
      (f.fiber (f x)).fromSpecResidueField (f.asFiber x) = f.asFiberHom x := by
  simpa only [Scheme.descResidueField, fiberResidueFieldToSourceResidueField,
    fiberStalkToSourceResidueField] using
      descResidueField_stalkClosedPointTo_congr (f.asFiberHom x) (f.asFiber x)
        (Scheme.Hom.asFiberHom_apply f x _)

/-- The residue-field map of the fibre inclusion, with its source identified
with `κ(x)`. This is the inverse residue-field comparison. -/
noncomputable def sourceResidueFieldToFiberResidueField
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    X.residueField x ⟶ fiberResidueFieldAt f x :=
  (X.residueFieldCongr (f.fiberι_asFiber x)).inv ≫
    (f.fiberι (f x)).residueFieldMap (f.asFiber x)

/-- The residue-field maps of the distinguished fibre point and fibre
inclusion compose to the identity on `κ(x)`. -/
theorem sourceResidueFieldToFiberResidueField_comp
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    (fiberResidueFieldToSourceResidueField f x).hom.comp
        (sourceResidueFieldToFiberResidueField f x).hom =
      RingHom.id (X.residueField x) := by
  have hcomp : sourceResidueFieldToFiberResidueField f x ≫
      fiberResidueFieldToSourceResidueField f x = 𝟙 (X.residueField x) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecResidueField x)).1
    simp only [Spec.map_comp, Category.assoc, Spec.map_id, Category.id_comp]
    rw [sourceResidueFieldToFiberResidueField]
    rw [Spec.map_comp, Category.assoc]
    simp only [Scheme.residueFieldCongr_inv,
      Scheme.residueFieldCongr_fromSpecResidueField]
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      ← Category.assoc, fiberResidueFieldToSourceResidueField_fromSpec,
      Scheme.Hom.asFiberHom_fiberι]
  exact congrArg CommRingCat.Hom.hom hcomp

/-- The induced map from the distinguished fibre residue field to `κ(x)` is
bijective. -/
theorem fiberResidueFieldToSourceResidueField_bijective
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Function.Bijective (fiberResidueFieldToSourceResidueField f x).hom := by
  refine ⟨(fiberResidueFieldToSourceResidueField f x).hom.injective, ?_⟩
  intro a
  exact ⟨(sourceResidueFieldToFiberResidueField f x).hom a,
    RingHom.congr_fun (sourceResidueFieldToFiberResidueField_comp f x) a⟩

/-- The residue-field equivalence at the distinguished fibre point commutes
with the canonical maps from `κ(f(x))`. -/
theorem fiberResidueFieldAlgEquiv_commutes
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (r : S.residueField (f x)) :
    (RingEquiv.ofBijective (fiberResidueFieldToSourceResidueField f x).hom
      (fiberResidueFieldToSourceResidueField_bijective f x))
        ((algebraMap (S.residueField (f x)) (fiberResidueFieldAt f x)) r) =
      (algebraMap (S.residueField (f x)) (X.residueField x)) r := by
  have hbase : Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField (f x)) (fiberResidueFieldAt f x))) =
      (f.fiber (f x)).fromSpecResidueField (f.asFiber x) ≫
        f.fiberToSpecResidueField (f x) := by
    change Spec.map
      (CommRingCat.ofHom (algebraMap (S.residueField (f x))
          ((f.fiberToSpecResidueField (f x)) (f.asFiber x)).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso _ _).inv ≫
        (f.fiberToSpecResidueField (f x)).residueFieldMap (f.asFiber x)) = _
    rw [Spec.map_comp, Spec.map_comp, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
      (f.fiberToSpecResidueField (f x)) (f.asFiber x)
  have h : CommRingCat.ofHom
      (algebraMap (S.residueField (f x)) (fiberResidueFieldAt f x)) ≫
      fiberResidueFieldToSourceResidueField f x = f.residueFieldMap x := by
    apply Spec.map_injective
    rw [Spec.map_comp, hbase, ← Category.assoc,
      fiberResidueFieldToSourceResidueField_fromSpec,
      Scheme.Hom.asFiberHom_fiberToSpecResidueField]
  exact congrArg (fun φ : S.residueField (f x) ⟶ X.residueField x => φ r) h

/-- The residue field of the distinguished fibre point is canonically
equivalent over `κ(f(x))` to the source residue field `κ(x)`. -/
noncomputable def fiberResidueFieldAlgEquiv
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fiberResidueFieldAt f x ≃ₐ[S.residueField (f x)] X.residueField x :=
  let e : fiberResidueFieldAt f x ≃+* X.residueField x :=
    RingEquiv.ofRingHom (fiberResidueFieldToSourceResidueField f x).hom
      (sourceResidueFieldToFiberResidueField f x).hom
      (sourceResidueFieldToFiberResidueField_comp f x)
      (by
        ext a
        apply (fiberResidueFieldToSourceResidueField f x).hom.injective
        exact RingHom.congr_fun (sourceResidueFieldToFiberResidueField_comp f x)
          ((fiberResidueFieldToSourceResidueField f x).hom a))
  @AlgEquiv.ofRingEquiv (S.residueField (f x)) (fiberResidueFieldAt f x)
    (X.residueField x) _ _ _ _ _ e (fiberResidueFieldAlgEquiv_commutes f x)

/-- The inverse residue-field equivalence is the map of the fibre inclusion. -/
@[simp]
theorem fiberResidueFieldAlgEquiv_symm_toRingHom
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    (fiberResidueFieldAlgEquiv f x).symm.toRingHom =
      (sourceResidueFieldToFiberResidueField f x).hom := rfl

/-- The induced map from the distinguished fibre residue field to `κ(x)`,
viewed as a linear map over the fibre stalk. -/
noncomputable def fiberResidueFieldToSourceResidueFieldLinearMap
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    fiberResidueFieldAt f x →ₗ[fiberStalkAt f x] X.residueField x :=
  (IsScalarTower.toAlgHom (fiberStalkAt f x) (fiberResidueFieldAt f x)
    (X.residueField x)).toLinearMap

/-- The action of the source stalk on `κ(x)` factors through the stalk of the
distinguished fibre point. -/
instance sourceStalkFiberStalkSourceResidueFieldIsScalarTower
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsScalarTower (X.presheaf.stalk x) (fiberStalkAt f x)
      (X.residueField x) := by
  apply IsScalarTower.of_algebraMap_eq'
  have h : sourceStalkToFiberStalk f x ≫ fiberStalkToSourceResidueField f x =
      X.residue x := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk x)).1
    rw [Spec.map_comp, Category.assoc,
      SpecMap_sourceStalkToFiberStalk_fromSpecStalk, ← Category.assoc]
    rw [← fiberStalkToSourceResidueField_factor, Spec.map_comp, Category.assoc]
    change (Spec.map (fiberResidueFieldToSourceResidueField f x) ≫
      (f.fiber (f x)).fromSpecResidueField (f.asFiber x)) ≫ f.fiberι (f x) = _
    rw [fiberResidueFieldToSourceResidueField_fromSpec, f.asFiberHom_fiberι]
    rfl
  exact (congrArg CommRingCat.Hom.hom h).symm

/-- The canonical map from the distinguished fibre stalk to `κ(x)` is
surjective. -/
theorem fiberStalkToSourceResidueField_surjective
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Function.Surjective (fiberStalkToSourceResidueField f x).hom := by
  intro a
  obtain ⟨b, hb⟩ := (f.fiber (f x)).residue_surjective (f.asFiber x)
    ((sourceResidueFieldToFiberResidueField f x).hom a)
  refine ⟨b, ?_⟩
  have h := RingHom.congr_fun (sourceResidueFieldToFiberResidueField_comp f x) a
  change (fiberResidueFieldToSourceResidueField f x).hom
    (((f.fiber (f x)).residue (f.asFiber x)).hom b) = a
  exact (congrArg (fiberResidueFieldToSourceResidueField f x).hom hb).trans h

end AlgebraicGeometry.Scheme.Hom
