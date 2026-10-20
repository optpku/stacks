/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.ConstantGroup
public import ReasLib.NumberTheory.AlgebraicNumbers
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.GroupAction
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Spectrum

/-!
# Galois pullback cover over `Spec AlgebraicNumbers.algebraicQ`

This module records the scheme
`U = Spec AlgebraicNumbers.algebraicQ ×_{Spec ℚ} Spec AlgebraicNumbers.algebraicQ` over `Spec AlgebraicNumbers.algebraicQ`, the
diagonal section, the discrete Galois action on the first factor, and the
constant group scheme of `Gal(AlgebraicNumbers.algebraicQ / ℚ)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme.PreRelation

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.GaloisPullback

/-- The base scheme `S = Spec AlgebraicNumbers.algebraicQ`. -/
abbrev base : Scheme.{0} := Spec (CommRingCat.of AlgebraicNumbers.algebraicQ)

/-- The base scheme is the spectrum of `AlgebraicNumbers.algebraicQ`. -/
theorem base_eq : base = Spec (CommRingCat.of AlgebraicNumbers.algebraicQ) := rfl

/-- The structure morphism `Spec AlgebraicNumbers.algebraicQ ⟶ Spec ℚ`. -/
abbrev specMapQ : Spec (CommRingCat.of AlgebraicNumbers.algebraicQ) ⟶ Spec (CommRingCat.of ℚ) :=
  FieldExtension.specMap ℚ AlgebraicNumbers.algebraicQ

/-- `specMapQ` is the canonical morphism induced by `ℚ ⟶ AlgebraicNumbers.algebraicQ`. -/
theorem specMapQ_eq : specMapQ = FieldExtension.specMap ℚ AlgebraicNumbers.algebraicQ := rfl

/-- The cover `U = Spec AlgebraicNumbers.algebraicQ ×_{Spec ℚ} Spec AlgebraicNumbers.algebraicQ` as a scheme over
`Spec AlgebraicNumbers.algebraicQ`, via the second projection. -/
def cover : Over base :=
  Over.mk (pullback.snd specMapQ specMapQ)

/-- The underlying scheme of the cover is the fibre product of two copies of
`Spec AlgebraicNumbers.algebraicQ` over `Spec ℚ`. -/
theorem cover_left :
    cover.left = pullback specMapQ specMapQ := rfl

/-- The structure morphism of the cover is the second projection of the fibre
product. -/
theorem cover_hom : cover.hom = pullback.snd specMapQ specMapQ := rfl

/-- The diagonal section `Spec AlgebraicNumbers.algebraicQ ⟶ U` as a morphism of schemes. -/
def sectionLeft : base ⟶ cover.left :=
  pullback.lift (𝟙 base) (𝟙 base) rfl

/-- `sectionLeft` is the pullback lift of the pair of identities. -/
theorem sectionLeft_eq :
    sectionLeft = pullback.lift (𝟙 base) (𝟙 base) rfl := rfl

/-- The diagonal section lies over `Spec AlgebraicNumbers.algebraicQ`. -/
theorem sectionHom_w : sectionLeft ≫ cover.hom = 𝟙 base := by
  exact pullback.lift_snd _ _ _

/-- The diagonal section `Spec AlgebraicNumbers.algebraicQ ⟶ U` as a morphism over
`Spec AlgebraicNumbers.algebraicQ`. -/
def sectionHom : Over.mk (𝟙 base) ⟶ cover :=
  Over.homMk sectionLeft sectionHom_w

/-- The underlying scheme morphism of `sectionHom` is `sectionLeft`. -/
theorem sectionHom_left : sectionHom.left = sectionLeft := rfl

/-- First-factor Galois action on `U` commutes with the left projection to
`Spec ℚ`. -/
theorem actionLeft_eq₁ (σ : AlgebraicNumbers.gal) :
    specMapQ ≫ 𝟙 (Spec (CommRingCat.of ℚ)) = (FieldExtension.Galois.specAut σ).hom ≫ specMapQ := by
  simpa only [specMapQ, FieldExtension.Galois.specAut_hom, Category.comp_id] using
    (FieldExtension.Galois.baseAut_over ℚ AlgebraicNumbers.algebraicQ σ⁻¹).symm

/-- The underlying scheme morphism of the Galois action of `σ` on `U`. -/
def actionLeft (σ : AlgebraicNumbers.gal) : cover.left ⟶ cover.left :=
  pullback.map specMapQ specMapQ specMapQ specMapQ
    (FieldExtension.Galois.specAut σ).hom (𝟙 base) (𝟙 (Spec (CommRingCat.of ℚ)))
    (actionLeft_eq₁ σ) rfl

/-- `actionLeft σ` is `pullback.map` of `FieldExtension.Galois.specAut σ` on the first factor and
the identity on the second factor. -/
theorem actionLeft_eq (σ : AlgebraicNumbers.gal) :
    actionLeft σ =
      pullback.map specMapQ specMapQ specMapQ specMapQ
        (FieldExtension.Galois.specAut σ).hom (𝟙 base) (𝟙 (Spec (CommRingCat.of ℚ)))
        (actionLeft_eq₁ σ) rfl := rfl

/-- The Galois action on `U` lies over `Spec AlgebraicNumbers.algebraicQ`. -/
theorem actionLeft_w (σ : AlgebraicNumbers.gal) : actionLeft σ ≫ cover.hom = cover.hom := by
  change actionLeft σ ≫ pullback.snd specMapQ specMapQ =
    pullback.snd specMapQ specMapQ
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The Galois action of `σ` as an automorphism of the scheme `U`. -/
def actionIso (σ : AlgebraicNumbers.gal) : cover.left ≅ cover.left where
  hom := actionLeft σ
  inv := actionLeft σ⁻¹
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `actionIso σ` is `actionLeft σ`. -/
theorem actionIso_hom (σ : AlgebraicNumbers.gal) : (actionIso σ).hom = actionLeft σ := rfl

/-- The inverse map of `actionIso σ` is `actionLeft σ⁻¹`. -/
theorem actionIso_inv (σ : AlgebraicNumbers.gal) : (actionIso σ).inv = actionLeft σ⁻¹ := rfl

/-- The action of `Gal(AlgebraicNumbers.algebraicQ / ℚ)` on `U` over `Spec AlgebraicNumbers.algebraicQ`,
acting on the first factor by `FieldExtension.Galois.specAut`. -/
def action : AlgebraicNumbers.gal →* Aut cover where
  toFun σ := Over.isoMk (actionIso σ) (actionLeft_w σ)
  map_one' := sorry
  map_mul' := sorry

/-- The underlying scheme morphism of `action σ` is `actionLeft σ`. -/
theorem action_hom (σ : AlgebraicNumbers.gal) : (action σ).hom.left = actionLeft σ := rfl

/-- The identity Galois element acts by the identity automorphism of the cover. -/
theorem action_one : action 1 = 1 := action.map_one

/-- A Galois element fixes a point of the pullback precisely when it is the identity. -/
theorem action_apply_eq_iff (σ : AlgebraicNumbers.gal) (u : cover.left) :
    (action σ).hom.left u = u ↔ σ = 1 := sorry

/-- The Galois action on the pullback is residue-field free. -/
instance instIsResidueFieldFree_action : IsResidueFieldFree action where
  residueFieldAut_ne_id u σ hσ hu :=
    False.elim (hσ ((action_apply_eq_iff σ u).mp hu))

/-- The Galois action on `U` is transitive on topological points. -/
theorem exists_action_eq (u v : cover.left) :
    ∃ σ : AlgebraicNumbers.gal, (action σ).hom.left u = v := sorry

/-- Every point of `U` is closed. -/
theorem mem_closedPoints_cover (u : cover.left) : u ∈ closedPoints cover.left :=
  sorry

/-- The absolute Galois group with the discrete topology, viewed as a constant
group scheme over `Spec AlgebraicNumbers.algebraicQ`. -/
def constantGroup : Grp (Over base) :=
  ConstantGroup.baseChange base (GrpCat.of AlgebraicNumbers.gal)

/-- `constantGroup` is the base change of the constant group scheme on `AlgebraicNumbers.gal`. -/
theorem constantGroup_eq :
    constantGroup = ConstantGroup.baseChange base (GrpCat.of AlgebraicNumbers.gal) := rfl

end AlgebraicGeometry.AlgebraicSpace.GaloisPullback
