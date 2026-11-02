/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms to affine schemes from global sections

The `Γ ⊣ Spec` adjunction identifies morphisms from a locally ringed space to
an affine scheme with contravariant maps on global sections.  This file owns
the transported equivalences, point formulas, and the complementary-open
affineness criterion.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- Definition 26.5.5: a locally ringed space is affine in the canonical `Γ ⊣ Spec` sense
exactly when it is isomorphic to the spectrum of some commutative ring. -/
@[stacks 01HW "affine locally ringed spaces"]
theorem isIso_toΓSpec_iff_exists_isoSpec (X : LocallyRingedSpace.{u}) :
    IsIso X.toΓSpec ↔
      ∃ R : CommRingCat.{u},
        Nonempty (X ≅ (Spec R).toLocallyRingedSpace) := by
  constructor
  · intro h
    exact ⟨Γ.obj (op X), ⟨@asIso _ _ _ _ X.toΓSpec h⟩⟩
  · rintro ⟨R, ⟨e⟩⟩
    exact ΓSpec.locallyRingedSpaceAdjunction.isIso_unit_app_of_iso (X := op R) e

namespace GlobalSections

/-- Morphisms `X ⟶ Spec R` are equivalent to ring maps `R ⟶ Γ(X)`. -/
@[stacks 01I1 "morphisms to an affine spectrum"]
noncomputable def homEquivSpec (X : LocallyRingedSpace.{u}) (R : CommRingCat.{u}) :
    (X ⟶ (Spec R).toLocallyRingedSpace) ≃
      (R ⟶ LocallyRingedSpace.Γ.obj (op X)) :=
  (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op R)).symm.trans
    (CategoryTheory.opEquiv _ _)

/-- `homEquivSpec` is the contravariant map on global sections after the
canonical affine comparison. -/
@[simp, stacks 01I1 "global-sections map to an affine spectrum"]
theorem homEquivSpec_apply (X : LocallyRingedSpace.{u}) (R : CommRingCat.{u})
    (f : X ⟶ (Spec R).toLocallyRingedSpace) :
    homEquivSpec X R f =
      (Scheme.ΓSpecIso R).inv ≫ LocallyRingedSpace.Γ.map f.op := by
  rfl

/-- The inverse of `homEquivSpec` is the morphism supplied by `Γ ⊣ Spec`. -/
@[simp, stacks 01I1 "affine spectrum morphism from global sections"]
theorem homEquivSpec_symm_apply (X : LocallyRingedSpace.{u}) (R : CommRingCat.{u})
    (phi : R ⟶ LocallyRingedSpace.Γ.obj (op X)) :
    (homEquivSpec X R).symm phi =
      ΓSpec.locallyRingedSpaceAdjunction.homEquiv X (op R) phi.op := by
  rfl

/-- Morphisms from `X` to an affine scheme `Y` are equivalent to maps
`Γ(Y) ⟶ Γ(X)`. -/
@[stacks 01I1]
noncomputable def homEquivAffine
    {X : LocallyRingedSpace.{u}} {Y : Scheme.{u}} [IsAffine Y] :
    (X ⟶ Y.toLocallyRingedSpace) ≃
      (Scheme.Γ.obj (op Y) ⟶ LocallyRingedSpace.Γ.obj (op X)) :=
  ((Iso.refl X).homCongr
      (Scheme.forgetToLocallyRingedSpace.mapIso Y.isoSpec)).trans <|
    (ΓSpec.locallyRingedSpaceAdjunction.homEquiv X
      (op (Scheme.Γ.obj (op Y)))).symm.trans <|
        CategoryTheory.opEquiv _ _

/-- `homEquivAffine` sends a morphism to its map on global sections. -/
@[simp, stacks 01I1 "affine-target global-sections map"]
theorem homEquivAffine_apply
    {X : LocallyRingedSpace.{u}} {Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y.toLocallyRingedSpace) :
    homEquivAffine f =
      (LocallyRingedSpace.Γ.map f.op :
        Scheme.Γ.obj (op Y) ⟶ LocallyRingedSpace.Γ.obj (op X)) := by
  change homEquivSpec X _ ((Iso.refl X).inv ≫ f ≫
    Scheme.Hom.toLRSHom Y.isoSpec.hom) = _
  rw [homEquivSpec_apply]
  simp only [Iso.refl_inv, Category.id_comp, op_comp, Functor.map_comp]
  change (Scheme.ΓSpecIso _).inv ≫ Y.toSpecΓ.appTop ≫ Γ.map f.op = _
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id_assoc]
  rfl

/-- The inverse affine Hom equivalence is the adjunction morphism followed by
the inverse affine comparison. -/
@[simp, stacks 01I1 "affine-target morphism from global sections"]
theorem homEquivAffine_symm_apply
    {X : LocallyRingedSpace.{u}} {Y : Scheme.{u}} [IsAffine Y]
    (phi : Scheme.Γ.obj (op Y) ⟶ LocallyRingedSpace.Γ.obj (op X)) :
    homEquivAffine.symm phi =
      ΓSpec.locallyRingedSpaceAdjunction.homEquiv X
          (op (Scheme.Γ.obj (op Y))) phi.op ≫
        Scheme.Hom.toLRSHom Y.isoSpec.inv := by
  change (Iso.refl X).hom ≫
    ΓSpec.locallyRingedSpaceAdjunction.homEquiv X
      (op (Scheme.Γ.obj (op Y))) phi.op ≫
        Scheme.Hom.toLRSHom Y.isoSpec.inv = _
  rw [Iso.refl_hom, Category.id_comp]

end GlobalSections

namespace Hom

/-- For a map to an affine scheme, the point map agrees with `Spec.map` after
the affine comparison. -/
@[stacks 01HY]
theorem isoSpec_apply
    {X : LocallyRingedSpace.{u}} {Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y.toLocallyRingedSpace) (x : X) :
    Y.isoSpec.hom (f.base x) =
      Spec.map (Γ.map f.op) (X.toΓSpecFun x) := by
  exact congrArg (fun g : X ⟶ _ => g.base x) (identityToΓSpec.naturality f)

/-- Receiver-style point formula for a map to an affine scheme. -/
@[stacks 01HY]
theorem apply_eq_isoSpec_inv
    {X : LocallyRingedSpace.{u}} {Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y.toLocallyRingedSpace) (x : X) :
    f.base x = Y.isoSpec.inv (Spec.map (Γ.map f.op) (X.toΓSpecFun x)) := by
  rw [← isoSpec_apply f x]
  exact (Scheme.hom_inv_apply Y.isoSpec (f.base x)).symm

end Hom

/-- A locally ringed space covered by complementary affine opens is affine in
the canonical `Γ ⊣ Spec` sense. -/
@[stacks 01I5]
theorem isIso_toΓSpec_of_isCompl
    {X : LocallyRingedSpace.{u}} {U V : Opens X}
    (hcompl : IsCompl U V)
    [IsIso (X.restrict U.isOpenEmbedding).toΓSpec]
    [IsIso (X.restrict V.isOpenEmbedding).toΓSpec] :
    IsIso X.toΓSpec := by
  let S : Scheme.{u} :=
    { toLocallyRingedSpace := X
      local_affine := by
        intro x
        have hx : x ∈ U ⊔ V := by
          rw [hcompl.sup_eq_top]
          trivial
        rcases hx with hx | hx
        · obtain ⟨R, hR⟩ :=
            (isIso_toΓSpec_iff_exists_isoSpec (X.restrict U.isOpenEmbedding)).mp inferInstance
          exact ⟨⟨U, hx⟩, R, hR⟩
        · obtain ⟨R, hR⟩ :=
            (isIso_toΓSpec_iff_exists_isoSpec (X.restrict V.isOpenEmbedding)).mp inferInstance
          exact ⟨⟨V, hx⟩, R, hR⟩ }
  have hU : IsAffineOpen (X := S) U := by
    refine ⟨(isIso_iff_of_reflects_iso _ Scheme.forgetToLocallyRingedSpace).mp ?_⟩
    change IsIso (X.restrict U.isOpenEmbedding).toΓSpec
    infer_instance
  have hV : IsAffineOpen (X := S) V := by
    refine ⟨(isIso_iff_of_reflects_iso _ Scheme.forgetToLocallyRingedSpace).mp ?_⟩
    change IsIso (X.restrict V.isOpenEmbedding).toΓSpec
    infer_instance
  have hsup : (U ⊔ V : S.Opens) = ⊤ := hcompl.sup_eq_top
  have htop : IsAffineOpen (⊤ : S.Opens) := by
    simpa only [hsup] using hU.sup_of_disjoint hV hcompl.disjoint
  letI : IsAffine (⊤ : S.Opens).toScheme := htop
  letI : IsAffine S := IsAffine.of_isIso S.topIso.inv
  exact Scheme.forgetToLocallyRingedSpace.map_isIso S.toSpecΓ

end AlgebraicGeometry.LocallyRingedSpace
