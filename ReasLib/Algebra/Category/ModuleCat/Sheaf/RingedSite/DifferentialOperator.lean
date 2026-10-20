/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.DifferentialOperator
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential Operators on Ringed Sites

This module restricts the objectwise presheaf predicate to sheaves of modules
over a morphism of commutative ring sheaves on a fixed site.  Keeping the
definition at the underlying-presheaf boundary makes restriction,
sheafification, and sectionwise evaluation share one API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O₁ O₂ : Sheaf J CommRingCat.{w}}

/-- An `O₁`-linear morphism between restrictions of `O₂`-module sheaves is a differential
operator of order at most `k` relative to `φ` when every map on sections has that order bound
over `O₁(X) → O₂(X)`. -/
@[stacks 09CR, stacks 0G3Q]
def IsDifferentialOperatorOfOrder
    (φ : O₁ ⟶ O₂) {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G) (k : ℕ) : Prop :=
  PresheafOfModules.IsDifferentialOperatorOfOrder φ.hom D.val k

namespace IsDifferentialOperatorOfOrder

/-- The sheaf predicate is exactly the differential-operator predicate on the
underlying module presheaves. -/
theorem iff_val
    (φ : O₁ ⟶ O₂) {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G) (k : ℕ) :
    IsDifferentialOperatorOfOrder φ D k ↔
      PresheafOfModules.IsDifferentialOperatorOfOrder φ.hom D.val k := sorry

/-- Evaluate a ringed-site differential operator at a section object. -/
theorem app
    (φ : O₁ ⟶ O₂) {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (X : Cᵒᵖ) :
    ModuleCat.IsDifferentialOperatorOfOrder (φ.hom.app X).hom (D.val.app X) k := sorry

/-- The zero morphism of restricted module sheaves has every differential-operator
order bound. -/
theorem zero (φ : O₁ ⟶ O₂)
    {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂} (k : ℕ) :
    IsDifferentialOperatorOfOrder φ (0 : (restrictionAlong φ).obj F ⟶
      (restrictionAlong φ).obj G) k := sorry

/-- The sum of two ringed-site differential operators with a common order bound
has that same order bound. -/
theorem add (φ : O₁ ⟶ O₂)
    {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    {D E : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G} {k : ℕ}
    (hD : IsDifferentialOperatorOfOrder φ D k)
    (hE : IsDifferentialOperatorOfOrder φ E k) :
    IsDifferentialOperatorOfOrder φ (D + E) k := sorry

/-- Negation preserves the ringed-site differential-operator order bound. -/
theorem neg (φ : O₁ ⟶ O₂)
    {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    {D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G} {k : ℕ}
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    IsDifferentialOperatorOfOrder φ (-D) k := sorry

/-- The identity morphism of a restricted module sheaf is a differential
operator of order zero. -/
theorem id (φ : O₁ ⟶ O₂)
    {F : ringedSiteModuleCategory.{u, v, z, w} J O₂} :
    IsDifferentialOperatorOfOrder φ (𝟙 ((restrictionAlong φ).obj F)) 0 := sorry

/-- Composing ringed-site differential operators adds their order bounds. -/
@[stacks 09CS, stacks 0G3R]
theorem comp (φ : O₁ ⟶ O₂)
    {F G H : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    {D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G}
    {E : (restrictionAlong φ).obj G ⟶ (restrictionAlong φ).obj H}
    {k l : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k)
    (hE : IsDifferentialOperatorOfOrder φ E l) :
    IsDifferentialOperatorOfOrder φ (D ≫ E) (k + l) := sorry

/-- A ringed-site differential operator has the successor order bound. -/
theorem le_succ (φ : O₁ ⟶ O₂)
    {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    {D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G} {k : ℕ}
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    IsDifferentialOperatorOfOrder φ D (k + 1) := sorry

/-- A ringed-site differential operator with order bound `k` has every larger
order bound. -/
theorem mono (φ : O₁ ⟶ O₂)
    {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    {D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G}
    {k l : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (hkl : k ≤ l) :
    IsDifferentialOperatorOfOrder φ D l := sorry

/-- Restriction of scalars sends an `O₂`-linear morphism to an order-zero differential
operator. -/
theorem restrictionAlong_map
    (φ : O₁ ⟶ O₂) {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂} (f : F ⟶ G) :
    IsDifferentialOperatorOfOrder φ ((restrictionAlong φ).map f) 0 := sorry

/-- Precomposition with an `O₂`-linear source morphism preserves a differential-operator
order bound. -/
theorem precompose
    (φ : O₁ ⟶ O₂)
    {F F' G : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (α : F' ⟶ F) {D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G}
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    IsDifferentialOperatorOfOrder φ ((restrictionAlong φ).map α ≫ D) k := sorry

/-- Postcomposition with an `O₂`-linear target morphism preserves a differential-operator
order bound. -/
theorem postcompose
    (φ : O₁ ⟶ O₂)
    {F G G' : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    {D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G}
    (hD : IsDifferentialOperatorOfOrder φ D k) (α : G ⟶ G') :
    IsDifferentialOperatorOfOrder φ (D ≫ (restrictionAlong φ).map α) k := sorry

end IsDifferentialOperatorOfOrder

namespace DifferentialOperators

/-- The additive subgroup of morphisms between scalar restrictions consisting of differential
operators of order at most `k`. -/
@[stacks 09CR "additive subgroup of bounded differential operators"]
noncomputable def addSubgroup
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) :
    AddSubgroup ((restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G) where
  carrier := { D | IsDifferentialOperatorOfOrder φ D k }
  zero_mem' := IsDifferentialOperatorOfOrder.zero φ k
  add_mem' := fun hD hE ↦ IsDifferentialOperatorOfOrder.add φ hD hE
  neg_mem' := fun hD ↦ IsDifferentialOperatorOfOrder.neg φ hD

/-- Membership in the bounded differential-operator subgroup is the order predicate. -/
@[simp]
theorem mem_addSubgroup_iff
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory.{u, v, z, w} J O₂)
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G) :
    D ∈ addSubgroup φ F k G ↔ IsDifferentialOperatorOfOrder φ D k := sorry

/-- Order-`k` differential operators from a fixed module sheaf `F` to a module sheaf `G`. -/
@[stacks 09CR "bounded differential operators"]
abbrev ofOrder
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) : Type _ :=
  addSubgroup φ F k G

/-- The restricted-scalar sheaf morphism underlying a bounded differential operator. -/
abbrev toHom
    {φ : O₁ ⟶ O₂} {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (D : ofOrder φ F k G) :
    (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G :=
  D.1

/-- Bundle a restricted-scalar sheaf morphism together with its differential-operator bound. -/
def ofHom
    {φ : O₁ ⟶ O₂} {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (hD : IsDifferentialOperatorOfOrder φ D k) : ofOrder φ F k G :=
  ⟨D, hD⟩

/-- The underlying morphism of a bounded operator satisfies its recorded order bound. -/
theorem toHom_isOfOrder
    {φ : O₁ ⟶ O₂} {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (D : ofOrder φ F k G) :
    IsDifferentialOperatorOfOrder φ (toHom D) k := sorry

/-- Bundling the underlying morphism of a bounded operator recovers that operator. -/
@[simp]
theorem ofHom_toHom
    {φ : O₁ ⟶ O₂} {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (D : ofOrder φ F k G) :
    ofHom (toHom D) (toHom_isOfOrder D) = D := sorry

/-- Taking the underlying morphism of a freshly bundled operator recovers the input. -/
@[simp]
theorem toHom_ofHom
    {φ : O₁ ⟶ O₂} {F G : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (D : (restrictionAlong φ).obj F ⟶ (restrictionAlong φ).obj G)
    (hD : IsDifferentialOperatorOfOrder φ D k) :
    toHom (ofHom D hD) = D := sorry

/-- Precompose a bounded differential operator with an `O₂`-linear source morphism. -/
noncomputable def precompose
    (φ : O₁ ⟶ O₂)
    {F F' G : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (α : F' ⟶ F) : ofOrder φ F k G → ofOrder φ F' k G :=
  fun D ↦ ofHom ((restrictionAlong φ).map α ≫ toHom D)
    (IsDifferentialOperatorOfOrder.precompose φ α (toHom_isOfOrder D))

/-- The underlying morphism of a precomposed differential operator. -/
@[simp]
theorem toHom_precompose
    (φ : O₁ ⟶ O₂)
    {F F' G : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (α : F' ⟶ F) (D : ofOrder φ F k G) :
    toHom (precompose φ α D) = (restrictionAlong φ).map α ≫ toHom D := sorry

/-- Precomposition sends the zero differential operator to zero. -/
theorem precompose_zero
    (φ : O₁ ⟶ O₂)
    {F F' G : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (α : F' ⟶ F) :
    precompose φ α (0 : ofOrder φ F k G) = 0 := sorry

/-- Precomposition preserves addition of bounded differential operators. -/
theorem precompose_add
    (φ : O₁ ⟶ O₂)
    {F F' G : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (α : F' ⟶ F) (D E : ofOrder φ F k G) :
    precompose φ α (D + E) = precompose φ α D + precompose φ α E := sorry

/-- Bounded differential operators, bundled as an object of `AddCommGrpCat`. -/
noncomputable abbrev group
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) : AddCommGrpCat :=
  AddCommGrpCat.of (ofOrder φ F k G)

/-- Precomposition by an identity acts identically on bounded differential operators. -/
theorem precompose_id
    (φ : O₁ ⟶ O₂) (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) :
    TypeCat.ofHom (precompose (G := G) (k := k) φ (𝟙 F)) =
      𝟙 (ofOrder φ F k G) := sorry

/-- Precomposition reverses composition of source morphisms. -/
theorem precompose_comp
    (φ : O₁ ⟶ O₂) (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    {F F' F'' : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (α : F' ⟶ F) (β : F'' ⟶ F') :
    TypeCat.ofHom (precompose (G := G) (k := k) φ (β ≫ α)) =
      TypeCat.ofHom (precompose (G := G) (k := k) φ α) ≫
        TypeCat.ofHom (precompose (G := G) (k := k) φ β) := sorry

/-- Precomposition as a morphism between the additive groups of bounded differential
operators. -/
noncomputable def sourceMap
    (φ : O₁ ⟶ O₂) (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    {F F' : ringedSiteModuleCategory.{u, v, z, w} J O₂} (α : F' ⟶ F) :
    group φ F k G ⟶ group φ F' k G :=
  AddCommGrpCat.ofHom
    { toFun := precompose φ α
      map_zero' := precompose_zero φ α
      map_add' := precompose_add φ α }

/-- The underlying operator of a source map is ordinary precomposition. -/
@[simp]
theorem toHom_sourceMap
    (φ : O₁ ⟶ O₂) (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    {F F' : ringedSiteModuleCategory.{u, v, z, w} J O₂} (α : F' ⟶ F)
    (D : ofOrder φ F k G) :
    toHom (sourceMap φ G k α D) = (restrictionAlong φ).map α ≫ toHom D := sorry

/-- Precomposition by an identity induces the identity on the operator group. -/
@[simp]
theorem sourceMap_id
    (φ : O₁ ⟶ O₂) (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) :
    sourceMap φ G k (𝟙 F) = 𝟙 (group φ F k G) := sorry

/-- Source maps reverse composition. -/
@[simp]
theorem sourceMap_comp
    (φ : O₁ ⟶ O₂) (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    {F F' F'' : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (α : F' ⟶ F) (β : F'' ⟶ F') :
    sourceMap φ G k (β ≫ α) = sourceMap φ G k α ≫ sourceMap φ G k β := sorry

/-- The `AddCommGrpCat`-valued contravariant functor of bounded differential operators into a
fixed target module sheaf. -/
@[stacks 09CT "contravariant additive differential-operator functor"]
noncomputable def sourceGroupFunctor
    (φ : O₁ ⟶ O₂) (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ) :
    (ringedSiteModuleCategory.{u, v, z, w} J O₂)ᵒᵖ ⥤ AddCommGrpCat where
  obj F := group φ F.unop k G
  map α := sourceMap φ G k α.unop
  map_id F := sorry
  map_comp α β := sorry

/-- Precomposition is additive in the source morphism. -/
theorem sourceMap_add
    (φ : O₁ ⟶ O₂) (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    {F F' : ringedSiteModuleCategory.{u, v, z, w} J O₂} (α β : F' ⟶ F) :
    sourceMap φ G k (α + β) = sourceMap φ G k α + sourceMap φ G k β := sorry

namespace sourceGroupFunctor

/-- The source-contravariant differential-operator functor is additive. -/
instance additive
    (φ : O₁ ⟶ O₂) (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ) :
    (sourceGroupFunctor φ G k).Additive := sorry

end sourceGroupFunctor

/-- The underlying contravariant Type-valued functor of bounded differential operators into a
fixed target module sheaf. -/
@[stacks 09CT "contravariant differential-operator functor"]
noncomputable def sourceFunctor
    (φ : O₁ ⟶ O₂) (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ) :
    (ringedSiteModuleCategory.{u, v, z, w} J O₂)ᵒᵖ ⥤ Type _ :=
  sourceGroupFunctor φ G k ⋙ CategoryTheory.forget AddCommGrpCat

/-- Postcompose a bounded differential operator with an `O₂`-linear target morphism. -/
noncomputable def postcompose
    (φ : O₁ ⟶ O₂)
    {F G G' : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (α : G ⟶ G') : ofOrder φ F k G → ofOrder φ F k G' :=
  fun D ↦ ofHom (toHom D ≫ (restrictionAlong φ).map α)
    (IsDifferentialOperatorOfOrder.postcompose φ (toHom_isOfOrder D) α)

/-- The underlying morphism of a postcomposed differential operator is ordinary
postcomposition. -/
@[simp]
theorem toHom_postcompose
    (φ : O₁ ⟶ O₂)
    {F G G' : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (α : G ⟶ G') (D : ofOrder φ F k G) :
    toHom (postcompose φ α D) =
      toHom D ≫ (restrictionAlong φ).map α := sorry

/-- Postcomposition sends the zero differential operator to zero. -/
theorem postcompose_zero
    (φ : O₁ ⟶ O₂)
    {F G G' : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (α : G ⟶ G') :
    postcompose (F := F) (k := k) φ α (0 : ofOrder φ F k G) = 0 := sorry

/-- Postcomposition preserves addition of bounded differential operators. -/
theorem postcompose_add
    (φ : O₁ ⟶ O₂)
    {F G G' : ringedSiteModuleCategory.{u, v, z, w} J O₂} {k : ℕ}
    (α : G ⟶ G') (D E : ofOrder φ F k G) :
    postcompose φ α (D + E) = postcompose φ α D + postcompose φ α E := sorry

/-- Postcomposition as a morphism between the additive groups of bounded differential
operators. -/
noncomputable def map
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    {G G' : ringedSiteModuleCategory.{u, v, z, w} J O₂} (α : G ⟶ G') :
    group φ F k G ⟶ group φ F k G' :=
  AddCommGrpCat.ofHom
    { toFun := postcompose φ α
      map_zero' := postcompose_zero φ α
      map_add' := postcompose_add φ α }

/-- Postcomposition by an identity induces the identity on the operator group. -/
@[simp]
theorem map_id
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory.{u, v, z, w} J O₂) :
    map φ F k (𝟙 G) = 𝟙 (group φ F k G) := sorry

/-- The additive-group morphisms induced by postcomposition respect composition. -/
@[simp]
theorem map_comp
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    {G G' G'' : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (α : G ⟶ G') (β : G' ⟶ G'') :
    map φ F k (α ≫ β) = map φ F k α ≫ map φ F k β := sorry

/-- The `AddCommGrpCat`-valued functor of bounded differential operators out of a fixed module
sheaf. -/
@[stacks 09CT "additive differential-operator functor"]
noncomputable def groupFunctor
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ) :
    ringedSiteModuleCategory.{u, v, z, w} J O₂ ⥤ AddCommGrpCat where
  obj G := group φ F k G
  map α := map φ F k α
  map_id G := map_id φ F k G
  map_comp α β := map_comp φ F k α β

/-- Postcomposition is additive in the target morphism. -/
theorem map_add
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    {G G' : ringedSiteModuleCategory.{u, v, z, w} J O₂} (α β : G ⟶ G') :
    map φ F k (α + β) = map φ F k α + map φ F k β := sorry

namespace groupFunctor

/-- The additive-group-valued differential-operator functor is additive. -/
instance additive
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ) :
    (groupFunctor φ F k).Additive := sorry

end groupFunctor

/-- The underlying Type-valued functor of bounded differential operators. -/
@[stacks 09CT "underlying differential-operator functor"]
noncomputable def functor
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ) :
    ringedSiteModuleCategory.{u, v, z, w} J O₂ ⥤ Type _ :=
  groupFunctor φ F k ⋙ CategoryTheory.forget AddCommGrpCat

/-- The underlying operator of the functorial image is postcomposition by the target
morphism. -/
@[simp]
theorem toHom_map
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory.{u, v, z, w} J O₂) (k : ℕ)
    {G G' : ringedSiteModuleCategory.{u, v, z, w} J O₂} (α : G ⟶ G')
    (D : ofOrder φ F k G) :
    toHom ((functor φ F k).map α D) =
      toHom D ≫ (restrictionAlong φ).map α := sorry

/-- Simultaneous precomposition in the source and postcomposition in the target. -/
noncomputable def bimap
    (φ : O₁ ⟶ O₂) (k : ℕ)
    {F F' G G' : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (α : F' ⟶ F) (β : G ⟶ G') : group φ F k G ⟶ group φ F' k G' :=
  sourceMap φ G k α ≫ map φ F' k β

/-- The underlying operator of a bifunctorial image is ordinary composition on both sides. -/
@[simp]
theorem toHom_bimap
    (φ : O₁ ⟶ O₂) (k : ℕ)
    {F F' G G' : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (α : F' ⟶ F) (β : G ⟶ G') (D : ofOrder φ F k G) :
    toHom (bimap φ k α β D) =
      (restrictionAlong φ).map α ≫ toHom D ≫ (restrictionAlong φ).map β := sorry

/-- Acting by identities in both variables gives the identity on bounded operators. -/
@[simp]
theorem bimap_id
    (φ : O₁ ⟶ O₂) (k : ℕ)
    (F G : ringedSiteModuleCategory.{u, v, z, w} J O₂) :
    bimap φ k (𝟙 F) (𝟙 G) = 𝟙 (group φ F k G) := sorry

/-- Simultaneous source and target maps compose functorially. -/
@[simp]
theorem bimap_comp
    (φ : O₁ ⟶ O₂) (k : ℕ)
    {F F' F'' G G' G'' : ringedSiteModuleCategory.{u, v, z, w} J O₂}
    (α : F' ⟶ F) (α' : F'' ⟶ F') (β : G ⟶ G') (β' : G' ⟶ G'') :
    bimap φ k (α' ≫ α) (β ≫ β') =
      bimap φ k α β ≫ bimap φ k α' β' := sorry

/-- The additive-group-valued bifunctor of bounded differential operators, contravariant in
the source and covariant in the target.  Its two partial functors are additive separately. -/
@[stacks 09CT "additive-group-valued differential-operator bifunctor"]
noncomputable def groupBifunctor
    (φ : O₁ ⟶ O₂) (k : ℕ) :
    (ringedSiteModuleCategory.{u, v, z, w} J O₂)ᵒᵖ ×
        ringedSiteModuleCategory.{u, v, z, w} J O₂ ⥤ AddCommGrpCat where
  obj P := group φ P.1.unop k P.2
  map α := bimap φ k α.1.unop α.2
  map_id P := sorry
  map_comp α β := sorry

/-- The Type-valued bifunctor of bounded differential operators, contravariant in the source
and covariant in the target. -/
@[stacks 09CT "differential-operator bifunctor"]
noncomputable def bifunctor
    (φ : O₁ ⟶ O₂) (k : ℕ) :
    (ringedSiteModuleCategory.{u, v, z, w} J O₂)ᵒᵖ ×
        ringedSiteModuleCategory.{u, v, z, w} J O₂ ⥤ Type _ :=
  groupBifunctor φ k ⋙ CategoryTheory.forget AddCommGrpCat

end DifferentialOperators

end SheafOfModules.RingedSite
