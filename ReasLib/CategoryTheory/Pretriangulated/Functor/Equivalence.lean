/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.ZeroKernel
public import ReasLib.CategoryTheory.Pretriangulated.Functor.FullyFaithful
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Functor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence Criteria from Compact Generators

This leaf combines the compact-generator full-faithfulness criterion with the zero-kernel
criterion for a right adjoint.  It also exposes the canonical comparison on shifted self-Homs
induced by an equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe uR vC uC vD uD

namespace CategoryTheory

namespace Equivalence

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

section Compact

variable [Preadditive C] [Preadditive D]

/-- An additive equivalence identifies compact objects.  This is stated as an equivalence so
both transport directions are available without rebuilding an argument from a quasi-inverse. -/
@[stacks 09S9 "equivalences preserve compact objects"]
theorem isCompactObject_obj_iff (e : C ≌ D) [e.functor.Additive] (X : C) :
    IsCompactObject (e.functor.obj X) ↔ IsCompactObject X := sorry

/-- An additive equivalence sends compact objects to compact objects. -/
@[stacks 09S9 "equivalences send compact objects to compact objects"]
theorem isCompactObject_obj (e : C ≌ D) [e.functor.Additive]
    (X : C) (hX : IsCompactObject X) :
    IsCompactObject (e.functor.obj X) :=
  (e.isCompactObject_obj_iff X).2 hX

end Compact

section Generator

variable [HasZeroMorphisms C] [HasZeroMorphisms D]
variable [HasShift C ℤ] [HasShift D ℤ]

/-- A shift-compatible equivalence identifies weak generators. -/
@[stacks 09S9 "equivalences preserve weak generators"]
theorem isWeakGenerator_obj_iff (e : C ≌ D)
    [e.functor.PreservesZeroMorphisms] [e.inverse.PreservesZeroMorphisms]
    [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ] (X : C) :
    IsWeakGenerator (e.functor.obj X) ↔ IsWeakGenerator X := by
  constructor
  · intro hX K hK
    have hFK : ¬ IsZero (e.functor.obj K) := fun h ↦
      hK (IsZero.of_full_of_faithful_of_isZero e.functor K h)
    obtain ⟨n, f, hf⟩ := hX hFK
    let t : e.functor.obj (K⟦n⟧) ≅ (e.functor.obj K)⟦n⟧ :=
      (e.functor.commShiftIso n).app K
    obtain ⟨g, hg⟩ := e.fullyFaithfulFunctor.map_surjective (f ≫ t.inv)
    refine ⟨n, g, ?_⟩
    intro h
    have hg0 : e.functor.map g = 0 := by simp [h]
    exact hf (zero_of_comp_mono t.inv (hg.symm.trans hg0))
  · intro hX K hK
    have hGK : ¬ IsZero (e.inverse.obj K) := fun h ↦
      hK ((e.functor.map_isZero h).of_iso (e.counitIso.app K).symm)
    obtain ⟨n, f, hf⟩ := hX hGK
    let t := (e.functor.commShiftIso n).app (e.inverse.obj K) ≪≫
      (shiftFunctor D n).mapIso (e.counitIso.app K)
    refine ⟨n, e.functor.map f ≫ t.hom, ?_⟩
    intro h
    apply hf
    exact e.functor.zero_of_map_zero f (zero_of_comp_mono t.hom h)

/-- A shift-compatible equivalence sends weak generators to weak generators. -/
@[stacks 09S9 "equivalences send weak generators to weak generators"]
theorem isWeakGenerator_obj (e : C ≌ D)
    [e.functor.PreservesZeroMorphisms] [e.inverse.PreservesZeroMorphisms]
    [e.functor.CommShift ℤ] [e.inverse.CommShift ℤ]
    (X : C) (hX : IsWeakGenerator X) :
    IsWeakGenerator (e.functor.obj X) :=
  (e.isWeakGenerator_obj_iff X).2 hX

end Generator

section SelfShift

variable [HasShift C ℤ] [HasShift D ℤ]

/-- The canonical map on shifted self-Homs induced by an equivalence and an identification of
the image of the source object with the chosen target object. -/
@[stacks 09S9 "shifted self-Hom comparison under an equivalence"]
def selfShiftMap (e : C ≌ D) [e.functor.CommShift ℤ]
    {X : C} {Y : D} (h : e.functor.obj X ≅ Y) (n : ℤ) :
    (X ⟶ X⟦n⟧) → (Y ⟶ Y⟦n⟧) :=
  e.shiftedHomMap h h n

/-- The shifted self-Hom comparison is given by conjugating the shifted image of the source
morphism by the chosen object identification. -/
@[simp]
theorem selfShiftMap_apply (e : C ≌ D) [e.functor.CommShift ℤ]
    {X : C} {Y : D} (h : e.functor.obj X ≅ Y) (n : ℤ)
    (f : X ⟶ X⟦n⟧) :
    e.selfShiftMap h n f =
      h.inv ≫ ShiftedHom.map f e.functor ≫ (shiftFunctor D n).map h.hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- An equivalence induces a bijection on every shifted self-Hom set. -/
theorem selfShiftMap_bijective (e : C ≌ D) [e.functor.CommShift ℤ]
    {X : C} {Y : D} (h : e.functor.obj X ≅ Y) (n : ℤ) :
    Function.Bijective (e.selfShiftMap h n) := by
  let t := (e.functor.commShiftIso n).app X ≪≫ (shiftFunctor D n).mapIso h
  change Function.Bijective (fun f : X ⟶ X⟦n⟧ ↦
    h.inv ≫ (e.functor.map f ≫ (e.functor.commShiftIso n).hom.app X) ≫
      (shiftFunctor D n).map h.hom)
  simpa only [t, Function.comp_def, Iso.homCongr_apply, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
    (h.homCongr t).bijective.comp (e.fullyFaithfulFunctor.map_bijective X (X⟦n⟧))

/-- The shifted self-Hom comparison induced by an additive linear equivalence, bundled as a
linear map. -/
noncomputable def selfShiftLinearMap {R : Type uR} [Ring R]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    {X : C} {Y : D} (h : e.functor.obj X ≅ Y) (n : ℤ) :
    (X ⟶ X⟦n⟧) →ₗ[R] (Y ⟶ Y⟦n⟧) :=
  e.shiftedHomLinearMap h h n

/-- An additive linear equivalence with a chosen image identification induces a linear equivalence on
every shifted self-Hom module.  For diagonal bimodules this is the Hochschild cohomology
comparison under a derived Morita equivalence. -/
@[stacks 09S9 "shifted self-Hom linear equivalence"]
noncomputable def selfShiftLinearEquiv {R : Type uR} [Ring R]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    {X : C} {Y : D} (h : e.functor.obj X ≅ Y) (n : ℤ) :
    (X ⟶ X⟦n⟧) ≃ₗ[R] (Y ⟶ Y⟦n⟧) :=
  e.shiftedHomLinearEquiv h h n

/-- The linear shifted self-Hom equivalence uses the same conjugated shifted image as the
underlying set-level comparison. -/
@[simp]
theorem selfShiftLinearEquiv_apply {R : Type uR} [Ring R]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    {X : C} {Y : D} (h : e.functor.obj X ≅ Y) (n : ℤ)
    (f : X ⟶ X⟦n⟧) :
    e.selfShiftLinearEquiv (R := R) h n f =
      h.inv ≫ ShiftedHom.map f e.functor ≫ (shiftFunctor D n).map h.hom := rfl

/-- The inverse shifted self-Hom equivalence is the explicit transport along the chosen
quasi-inverse. -/
@[simp]
theorem selfShiftLinearEquiv_symm_apply {R : Type uR} [Ring R]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (e : C ≌ D) [e.functor.CommShift ℤ] [e.functor.Additive] [e.functor.Linear R]
    {X : C} {Y : D} (h : e.functor.obj X ≅ Y) (n : ℤ)
    (f : Y ⟶ Y⟦n⟧) :
    (e.selfShiftLinearEquiv (R := R) h n).symm f =
      e.shiftedHomInverseMap h h n f := rfl

end SelfShift

end Equivalence

namespace Adjunction

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [HasZeroObject C] [HasZeroObject D]
variable [HasZeroMorphisms D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable {F : C ⥤ D} {G : D ⥤ C}
variable [F.CommShift ℤ] [G.CommShift ℤ]

/-- If the image of an object weakly generates the target, then the right adjoint has zero
kernel.  Shift compatibility of the right adjoint supplies the formerly ad hoc bridge from a
zero right-adjoint value to vanishing shifted Homs. -/
@[stacks 09S7 "weak-generator zero-kernel criterion"]
theorem kernel_le_isZero_of_image_isWeakGenerator
    (adj : F ⊣ G) (E : C) (h_generator : IsWeakGenerator (F.obj E)) :
    G.kernel ≤ IsZero := by
  -- Only the source lacks specified zero morphisms; use those induced by its zero object.
  letI : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
  intro K hK
  by_contra h
  obtain ⟨n, f, hf⟩ := h_generator h
  have hGn : IsZero (G.obj (K⟦n⟧)) :=
    ((shiftFunctor C n).map_isZero hK).of_iso ((G.commShiftIso n).app K)
  exact hf ((adj.homEquiv E (K⟦n⟧)).injective (hGn.eq_of_tgt _ _))

end Adjunction

namespace Functor.IsEquivalence

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [HasZeroObject C] [HasZeroObject D]
variable [Preadditive C] [Preadditive D]
variable [HasCoproducts.{vC} C] [HasCoproducts.{vD} D]
variable [HasShift C ℤ] [HasShift D ℤ]
variable [∀ n : ℤ, (shiftFunctor C n).Additive]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]
variable [Pretriangulated C] [Pretriangulated D]
variable {F : C ⥤ D} {G : D ⥤ C}
variable [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated]

/-- A triangulated left adjoint is an equivalence when one compact source object localizing-
generates and detects isomorphisms, its image is a compact weak generator, and the functor is
bijective on every shifted self-Hom of the source generator. -/
@[stacks 09S7 "compact-generator equivalence criterion"]
theorem ofCompactGenerator
    (adj : F ⊣ G) (E : C)
    (h_localizing : (ObjectProperty.singleton E).IsLocalizingGenerator)
    (h_detecting : ((ObjectProperty.singleton E).shiftClosure ℤ).IsDetecting)
    (h_source_compact : IsCompactObject E)
    (h_target_compact : IsCompactObject (F.obj E))
    (h_target_generator : IsWeakGenerator (F.obj E))
    (h_ext : F.IsFullyFaithfulOnSelfShifts E) :
    F.IsEquivalence := sorry

end Functor.IsEquivalence

end CategoryTheory
