/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialOperator

/-!
# Finite-order differential operators on ringed sites

Finite-order differential operators are restricted-scalar morphisms which have some finite
order bound. They form additive groups and are closed under identities and composition.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.DifferentialOperators

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- The additive subgroup of restricted-scalar morphisms which are differential operators of
some finite order. -/
noncomputable def finiteOrderAddSubgroup
    (φ : O₁ ⟶ O₂) (F G : ringedSiteModuleCategory.{u, v, z, w} J O₂) :
    AddSubgroup ((restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G) where
  carrier := { D | ∃ k : ℕ, IsDifferentialOperatorOfOrder φ D k }
  zero_mem' := ⟨0, IsDifferentialOperatorOfOrder.zero φ 0⟩
  add_mem' := by
    rintro D E ⟨k, hD⟩ ⟨l, hE⟩
    refine ⟨k + l, IsDifferentialOperatorOfOrder.add φ ?_ ?_⟩
    · exact IsDifferentialOperatorOfOrder.mono φ hD (Nat.le_add_right k l)
    · exact IsDifferentialOperatorOfOrder.mono φ hE (Nat.le_add_left l k)
  neg_mem' := by
    rintro D ⟨k, hD⟩
    exact ⟨k, IsDifferentialOperatorOfOrder.neg φ hD⟩

/-- Finite-order differential operators between two module sheaves on a ringed site. -/
abbrev FiniteOrder
    (φ : O₁ ⟶ O₂) (F G : ringedSiteModuleCategory.{u, v, z, w} J O₂) : Type _ :=
  finiteOrderAddSubgroup φ F G

namespace FiniteOrder

/-- Regard a bounded differential operator as a finite-order differential operator. -/
def ofOrder {k : ℕ} {φ : O₁ ⟶ O₂}
    {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (D : DifferentialOperators.ofOrder φ F k G) :
    FiniteOrder φ F G :=
  ⟨D.1, k, D.2⟩

/-- The restricted-scalar morphism underlying a finite-order differential operator. -/
abbrev toHom {φ : O₁ ⟶ O₂}
    {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂} (D : FiniteOrder φ F G) :
    (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G :=
  D.1

/-- The underlying morphism of a finite-order differential operator has a finite order bound. -/
theorem toHom_isFiniteOrder {φ : O₁ ⟶ O₂}
    {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂} (D : FiniteOrder φ F G) :
    ∃ k : ℕ, IsDifferentialOperatorOfOrder φ (toHom D) k :=
  D.2

/-- Finite-order differential operators are equal when their underlying morphisms are equal. -/
@[ext]
theorem ext {φ : O₁ ⟶ O₂}
    {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂} {D E : FiniteOrder φ F G}
    (h : toHom D = toHom E) : D = E :=
  Subtype.ext h

/-- The identity finite-order differential operator. -/
def id (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) :
    FiniteOrder φ F F :=
  ⟨𝟙 ((restrictionAlong φ).obj F), 0, IsDifferentialOperatorOfOrder.id φ⟩

/-- Composition of finite-order differential operators. -/
def comp {φ : O₁ ⟶ O₂} {F G H : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (D : FiniteOrder φ F G) (E : FiniteOrder φ G H) : FiniteOrder φ F H := by
  refine ⟨toHom D ≫ toHom E, ?_⟩
  obtain ⟨k, hD⟩ := toHom_isFiniteOrder D
  obtain ⟨l, hE⟩ := toHom_isFiniteOrder E
  exact ⟨k + l, IsDifferentialOperatorOfOrder.comp φ hD hE⟩

/-- Forgetting the finite-order wrapper around a bounded operator recovers its morphism. -/
@[simp]
theorem toHom_ofOrder {k : ℕ} {φ : O₁ ⟶ O₂}
    {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (D : DifferentialOperators.ofOrder φ F k G) :
    toHom (ofOrder D) = DifferentialOperators.toHom D :=
  rfl

/-- The underlying morphism of the finite-order identity is the identity. -/
@[simp]
theorem toHom_id (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) :
    toHom (id φ F) = 𝟙 ((restrictionAlong φ).obj F) :=
  rfl

/-- The underlying morphism of a composite is the composite of the underlying morphisms. -/
@[simp]
theorem toHom_comp {φ : O₁ ⟶ O₂}
    {F G H : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (D : FiniteOrder φ F G) (E : FiniteOrder φ G H) :
    toHom (comp D E) = toHom D ≫ toHom E :=
  rfl

/-- A restricted-scalar morphism is the underlying morphism of a finite-order differential
operator exactly when it has some finite differential-operator order. -/
theorem exists_toHom_eq_iff (φ : O₁ ⟶ O₂)
    {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (f : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G) :
    (∃ D : FiniteOrder φ F G, toHom D = f) ↔
      ∃ k : ℕ, IsDifferentialOperatorOfOrder φ f k := by
  constructor
  · rintro ⟨D, rfl⟩
    exact toHom_isFiniteOrder D
  · intro hf
    exact ⟨⟨f, hf⟩, rfl⟩

end FiniteOrder

end SheafOfModules.RingedSite.DifferentialOperators
