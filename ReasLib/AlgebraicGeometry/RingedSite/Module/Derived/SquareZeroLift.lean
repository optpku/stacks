/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.MapObstruction

/-!
# Bounded-above lifts along square-zero surjections

A lift is a bounded-above derived module equipped with an identification of its derived
reduction. Compatible isomorphisms of lifts have explicit identity, inverse and composition.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open DerivedCategory
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived)
open SheafOfModules.RingedSite
open scoped CategoryTheory.DerivedCategory.DerivedTensor
open scoped DerivedExt

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, `DerivedTensor.Right.functor`, and `moduleDerivedAdjunction` must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): `monoidalCategory` is reducible to `KFlat.monoidalCategory` at the pinned `moduleCat_hasDerivedCategory`; `ρ_`, whiskering, `tensorLeft`, `mapUnitIso`, and the Ext target of `mapObstruction` must share that tensor.
attribute [local instance] monoidalCategory

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]

variable {𝒪 𝒪₀ : Sheaf J CommRingCat.{w}} (π : 𝒪 ⟶ 𝒪₀)
variable [Sheaf.IsLocallySurjective π]
variable (h_sq : KernelIdeal.IsSquareZero π)
variable [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))]
variable [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))]
variable [∀ K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) ℤ,
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))) (up ℤ)]
variable [∀ K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ,
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))) (up ℤ)]
variable [@DerivedTensor.Right.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) _ _ _ _ _ _]
variable [@DerivedTensor.Left.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) _ _ _ _ _ _]
variable [@DerivedTensor.Right.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
variable [@DerivedTensor.Left.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{w} (sameSiteHom π))
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))]
variable [DerivedAdjunction.HasPair.{w} (sameSiteHom π)]
variable [KFlat.HomotopyTensorDescends 𝒪]
variable [KFlat.TensorDescends 𝒪]
variable [KFlat.IsLocalization 𝒪]
variable [KFlat.HomotopyTensorDescends 𝒪₀]
variable [KFlat.TensorDescends 𝒪₀]
variable [KFlat.IsLocalization 𝒪₀]
variable [Tensor.Has 𝒪₀]
variable [(tensorO0 π).OplaxMonoidal]
variable [(pushforwardO0 π).CommShift ℤ]
variable [∀ (L : ModuleDerived.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)), (tensorLeft L).CommShift ℤ]
variable [∀ (L : ModuleDerived.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (M : ModuleDerived.{w, u, v, w}
      (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)),
  IsIso ((moduleDerivedAdjunction.{w} (sameSiteHom π)).projectionFormulaMate L M)]
variable [IsIso (pushforwardSingleUnit π (unitModule J 𝒪₀))]

/-- A lift of `K₀` along `π` is a bounded-above object of `D(𝒪)` together with an identification
of its derived extension of scalars with `K₀`. -/
structure Lift (h_sq : KernelIdeal.IsSquareZero π)
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) where
  /-- The underlying object of `D⁻(𝒪)`. -/
  object : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)
  /-- The comparison isomorphism `object ⊗ᴸ 𝒪₀ ≅ K₀` in `D(𝒪₀)`. -/
  iso : (tensorO0 π).obj object ≅ K₀
  /-- The underlying object is bounded above. -/
  object_isBoundedAbove : object.IsBoundedAbove

namespace Lift

/-- Assemble a lift from a bounded-above complex and a derived-extension isomorphism. -/
def of {K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)}
    (object : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (iso : (tensorO0 π).obj object ≅ K₀)
    (object_isBoundedAbove : object.IsBoundedAbove) :
    Lift π h_sq K₀ :=
  ⟨object, iso, object_isBoundedAbove⟩

/-- A lift consists of a bounded-above object of `D(𝒪)` and an isomorphism after `⊗ᴸ 𝒪₀`. -/
theorem spec {K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)}
    (L : Lift π h_sq K₀) :
    Nonempty ((tensorO0 π).obj L.object ≅ K₀) ∧ L.object.IsBoundedAbove := sorry

/-- `Lift.of` recovers the supplied object and comparison isomorphism. -/
theorem of_spec {K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)}
    (object : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (iso : (tensorO0 π).obj object ≅ K₀)
    (h : object.IsBoundedAbove) :
    (of π h_sq object iso h).object = object ∧
      (of π h_sq object iso h).iso = iso := sorry

end Lift

variable {K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)}

/-- An isomorphism of lifts is an isomorphism of underlying objects compatible with the
comparison isomorphisms. -/
structure LiftIso (L₁ L₂ : Lift π h_sq K₀) where
  /-- The underlying isomorphism in `D(𝒪)`. -/
  iso : L₁.object ≅ L₂.object
  /-- Derived extension of scalars intertwines the comparison isomorphisms. -/
  comm : (tensorO0 π).map iso.hom ≫ L₂.iso.hom = L₁.iso.hom

/-- Assemble an isomorphism of lifts from a compatible isomorphism of underlying objects. -/
def LiftIso.of (L₁ L₂ : Lift π h_sq K₀) (iso : L₁.object ≅ L₂.object)
    (comm : (tensorO0 π).map iso.hom ≫ L₂.iso.hom = L₁.iso.hom) :
    LiftIso π h_sq L₁ L₂ :=
  ⟨iso, comm⟩

/-- The compatibility square of an isomorphism of lifts. -/
theorem LiftIso.comm_spec {L₁ L₂ : Lift π h_sq K₀} (φ : LiftIso π h_sq L₁ L₂) :
    (tensorO0 π).map φ.iso.hom ≫ L₂.iso.hom = L₁.iso.hom := sorry

/-- The identity compatible isomorphism of a lift. -/
def LiftIso.refl (L : Lift π h_sq K₀) : LiftIso π h_sq L L where
  iso := Iso.refl L.object
  comm := by simp

/-- The inverse of a compatible isomorphism of lifts. -/
def LiftIso.symm {L₁ L₂ : Lift π h_sq K₀} (φ : LiftIso π h_sq L₁ L₂) :
    LiftIso π h_sq L₂ L₁ where
  iso := φ.iso.symm
  comm := by
    change (tensorO0 π).map φ.iso.inv ≫ L₁.iso.hom = L₂.iso.hom
    rw [← φ.comm, ← Category.assoc, ← Functor.map_comp, φ.iso.inv_hom_id,
      (tensorO0 π).map_id, Category.id_comp]

/-- The composite of compatible isomorphisms of lifts. -/
def LiftIso.trans {L₁ L₂ L₃ : Lift π h_sq K₀}
    (φ : LiftIso π h_sq L₁ L₂) (ψ : LiftIso π h_sq L₂ L₃) :
    LiftIso π h_sq L₁ L₃ where
  iso := φ.iso ≪≫ ψ.iso
  comm := by
    simp only [Iso.trans_hom, Functor.map_comp, Category.assoc, ψ.comm, φ.comm]

end

end RingedSite.Hom.ModuleDerived
