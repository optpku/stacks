/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Ring
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.FiniteFreeRetract
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Pullback on the Grothendieck ring of vector bundles

This module constructs the contravariant pullback ring homomorphism on the
Grothendieck ring of finite locally free modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.VectorBundleK0

variable {X Y Z : Scheme.{u}}

/-- Pull a finite locally free module back along a morphism of schemes. -/
noncomputable def pullbackObj (f : X ⟶ Y)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules)) :
    ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) :=
  ⟨(Scheme.Modules.pullback f).obj E.obj,
    @Scheme.Modules.pullback_isFiniteLocallyFree X Y f E.obj E.property⟩

/-- The underlying module of `pullbackObj f E` is the ordinary module pullback. -/
theorem pullbackObj_obj (f : X ⟶ Y)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules)) :
    (pullbackObj f E).obj = (Scheme.Modules.pullback f).obj E.obj := rfl

/-- Pullback classes kill the short-exact relations defining vector-bundle `K₀`. -/
theorem relations_le_ker_pullback (f : X ⟶ Y) :
    ObjectProperty.GrothendieckGroup.relations
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules) ≤
      (FreeAbelianGroup.lift fun E : ObjectProperty.FullSubcategory
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules) ↦
        ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
          (pullbackObj f E)).ker := sorry

/-- The additive pullback on the Grothendieck group of vector bundles. -/
noncomputable def pullbackAdd (f : X ⟶ Y) : VectorBundleK0 Y →+ VectorBundleK0 X :=
  ObjectProperty.GrothendieckGroup.lift
    (fun E ↦ ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) (pullbackObj f E))
    (relations_le_ker_pullback f)

/-- Additive pullback sends a vector-bundle generator to its pulled-back class. -/
theorem pullbackAdd_of (f : X ⟶ Y)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules)) :
    pullbackAdd f (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules) E) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
        (pullbackObj f E) := by
  exact FreeAbelianGroup.lift_apply_of _ E

private theorem class_eq_of_iso
    {E F : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)}
    (e : E.obj ≅ F.obj) :
    ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) F := by
  let M : X.Modules := CategoryTheory.Limits.terminal X.Modules
  have hM : CategoryTheory.Limits.IsZero M := by
    apply (CategoryTheory.Limits.IsZero.iff_id_eq_zero _).2
    exact (CategoryTheory.Limits.terminalIsTerminal (C := X.Modules)).hom_ext _ _
  letI : SheafOfModules.IsFiniteLocallyFree
      (SheafOfModules.unit X.ringCatSheaf) := (unitObject X).property
  let r : Retract M (SheafOfModules.unit X.ringCatSheaf) :=
    { i := 0, r := 0, retract := hM.eq_of_src _ _ }
  let Z : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) :=
    ⟨M, SheafOfModules.IsFiniteLocallyFree.ofRetract
      (X := X.toLocallyRingedSpace) r⟩
  exact ObjectProperty.GrothendieckGroup.of_iso Z hM
    (ObjectProperty.isoMk _ e)

private theorem addHom_ext {M : Type*} [AddCommGroup M]
    {p q : VectorBundleK0 X →+ M}
    (h : ∀ E, p (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
        q (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E)) : p = q := by
  apply QuotientAddGroup.addMonoidHom_ext
  exact FreeAbelianGroup.lift_ext _ _ h

/-- Additive pullback preserves the tensor-unit class. -/
theorem pullbackAdd_map_one (f : X ⟶ Y) :
    pullbackAdd f (1 : VectorBundleK0 Y) = 1 := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  letI : (TopologicalSpace.Opens.map f.base).Final :=
    CategoryTheory.final_of_representablyFlat (TopologicalSpace.Opens.map f.base)
  change pullbackAdd f (ObjectProperty.GrothendieckGroup.of
    (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules) (unitObject Y)) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) (unitObject X)
  rw [pullbackAdd_of]
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit
    (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom)
  exact class_eq_of_iso e

/-- Additive pullback preserves tensor-induced multiplication. -/
theorem pullbackAdd_map_mul (f : X ⟶ Y) (a b : VectorBundleK0 Y) :
    pullbackAdd f (a * b) = pullbackAdd f a * pullbackAdd f b := sorry

/-- Pullback on the Grothendieck ring of finite locally free modules. -/
noncomputable def pullback (f : X ⟶ Y) : VectorBundleK0 Y →+* VectorBundleK0 X :=
  { pullbackAdd f with
    map_one' := pullbackAdd_map_one f
    map_mul' := pullbackAdd_map_mul f }

/-- The additive part of vector-bundle `K₀` pullback is `pullbackAdd`. -/
theorem pullback_toAddMonoidHom (f : X ⟶ Y) :
    (pullback f).toAddMonoidHom = pullbackAdd f := rfl

/-- Pullback sends a vector-bundle generator to its pulled-back class. -/
theorem pullback_of (f : X ⟶ Y)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules)) :
    pullback f (ObjectProperty.GrothendieckGroup.of
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Y.Modules) E) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)
        (pullbackObj f E) :=
  pullbackAdd_of f E

/-- Pullback along the identity is the identity on vector-bundle `K₀`. -/
theorem pullback_id (X : Scheme.{u}) :
    pullback (𝟙 X) = RingHom.id (VectorBundleK0 X) := by
  apply RingHom.coe_addMonoidHom_injective
  apply addHom_ext
  intro E
  change pullback (𝟙 X) (ObjectProperty.GrothendieckGroup.of
    (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E
  rw [pullback_of]
  exact class_eq_of_iso ((Scheme.Modules.pullbackId X).app E.obj)

/-- Vector-bundle `K₀` pullback is contravariantly functorial under composition. -/
theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) = (pullback f).comp (pullback g) := by
  apply RingHom.coe_addMonoidHom_injective
  apply addHom_ext
  intro E
  change pullback (f ≫ g) (ObjectProperty.GrothendieckGroup.of
    (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Z.Modules) E) =
      pullback f (pullback g (ObjectProperty.GrothendieckGroup.of
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty Z.Modules) E))
  rw [pullback_of, pullback_of, pullback_of]
  exact class_eq_of_iso ((Scheme.Modules.pullbackComp f g).app E.obj).symm

end AlgebraicGeometry.Scheme.VectorBundleK0
