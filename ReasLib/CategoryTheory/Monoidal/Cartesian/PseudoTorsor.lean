/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {G : C} [GrpObj G]

/-- A module object is a pseudo-torsor when its shear morphism
`(g, x) ↦ (g • x, x)` is an isomorphism. -/
class IsPseudoTorsor (X : Mod C G) : Prop where
  /-- The shear morphism of a pseudo-torsor is an isomorphism. -/
  isIso_leftSMul : IsIso (ModObj.leftSMul G X.X)

namespace IsPseudoTorsor

/-- The shear morphism of a pseudo-torsor is an isomorphism. -/
instance instIsIsoLeftSMul (X : Mod C G) [IsPseudoTorsor X] :
    IsIso (ModObj.leftSMul G X.X) :=
  IsPseudoTorsor.isIso_leftSMul

/-- Pseudo-torsorhood transports across an equivariant isomorphism. -/
theorem ofIso {X Y : Mod C G} [IsPseudoTorsor X] (e : X ≅ Y) :
    IsPseudoTorsor Y := by
  constructor
  rw [ModObj.isIso_leftSMul_iff]
  intro Z x y
  obtain ⟨g, hg, hgu⟩ :=
    (ModObj.isIso_leftSMul_iff.mp
      (inferInstance : IsIso (ModObj.leftSMul G X.X))) Z
      (x ≫ e.inv.hom) (y ≫ e.inv.hom)
  have h_inv : e.inv.hom ≫ e.hom.hom = 𝟙 Y.X := by
    simpa only [Mod.comp_hom', Mod.id_hom'] using
      congrArg Mod.Hom.hom e.inv_hom_id
  refine ⟨g, ?_, ?_⟩
  · change g • x = y
    calc
      g • x = (g • x) ≫ (e.inv.hom ≫ e.hom.hom) := by rw [h_inv, Category.comp_id]
      _ = (g • (x ≫ e.inv.hom)) ≫ e.hom.hom := by
        rw [← Category.assoc, IsModHom.map_smul]
      _ = (y ≫ e.inv.hom) ≫ e.hom.hom := by rw [hg]
      _ = y := by rw [Category.assoc, h_inv, Category.comp_id]
  · intro g' hg'
    show g' = g
    apply hgu g'
    calc
      g' • (x ≫ e.inv.hom) = (g' • x) ≫ e.inv.hom :=
        (IsModHom.map_smul e.inv.hom g' x).symm
      _ = y ≫ e.inv.hom := by rw [hg']

end IsPseudoTorsor

open scoped MonObj in
/-- The regular left action of a group object is a pseudo-torsor. -/
instance instIsPseudoTorsorRegular : IsPseudoTorsor (regular G) := by
  constructor
  rw [ModObj.isIso_leftSMul_iff]
  change ∀ (Z : C) (x y : Z ⟶ G), ∃! g : Z ⟶ G, g * x = y
  intro Z x y
  refine ⟨y / x, div_mul_cancel y x, ?_⟩
  intro g hg
  show g = y / x
  exact eq_div_iff_mul_eq'.2 hg

/-- Pseudo-torsorhood is equivalent to invertibility of the shear morphism. -/
theorem isPseudoTorsor_iff (X : Mod C G) :
    IsPseudoTorsor X ↔ IsIso (ModObj.leftSMul G X.X) :=
  ⟨fun hX ↦ hX.isIso_leftSMul, fun hX ↦ ⟨hX⟩⟩

/-- Pseudo-torsorhood is equivalent to unique transitivity on generalized points. -/
theorem isPseudoTorsor_iff_forall_existsUnique_smul (X : Mod C G) :
    IsPseudoTorsor X ↔
      ∀ (Z : C) (x y : Z ⟶ X.X), ∃! g : Z ⟶ G, g • x = y :=
  (isPseudoTorsor_iff X).trans ModObj.isIso_leftSMul_iff

/-- A module object is trivial when it is equivariantly isomorphic to the regular left action. -/
abbrev IsTrivial (X : Mod C G) : Prop :=
  Nonempty (regular G ≅ X)

/-- Triviality is existence of an equivariant isomorphism from the regular left action. -/
theorem isTrivial_iff (X : Mod C G) :
    IsTrivial X ↔ Nonempty (regular G ≅ X) := Iff.rfl

namespace IsTrivial

/-- Every trivial module object is a pseudo-torsor. -/
theorem isPseudoTorsor {X : Mod C G} (hX : IsTrivial X) :
    IsPseudoTorsor X := by
  obtain ⟨e⟩ := hX
  exact IsPseudoTorsor.ofIso e

end IsTrivial

end CategoryTheory.Mod
