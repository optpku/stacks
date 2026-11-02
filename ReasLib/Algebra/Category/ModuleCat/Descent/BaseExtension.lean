/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor

/-!
# Descent for modules along a ring homomorphism

This file specializes the canonical descent-data functor of the extension-of-scalars
pseudofunctor to a single homomorphism of commutative rings.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The singleton family in `CommRingCatᵒᵖ` associated to a ring homomorphism
`f : R →+* S`. -/
def descentFamily (f : R →+* S) :
    PUnit.{1} → (Opposite.op (CommRingCat.of S) ⟶ Opposite.op (CommRingCat.of R)) :=
  fun _ ↦ (CommRingCat.ofHom f).op

/-- Every member of the singleton descent family is the opposite of the given ring
homomorphism. -/
@[simp]
theorem descentFamily_apply (f : R →+* S) (i : PUnit.{1}) :
    descentFamily f i = (CommRingCat.ofHom f).op := rfl

/-- The category of descent data for modules along `f : R →+* S`. -/
abbrev DescentData (f : R →+* S) :=
  Pseudofunctor.DescentData (C := CommRingCat.{u}ᵒᵖ) (ι := PUnit.{1})
    (S := Opposite.op (CommRingCat.of R))
    (X := fun _ ↦ Opposite.op (CommRingCat.of S))
    ((unopUnop CommRingCat.{u}).toPseudofunctor.comp
      CommRingCat.moduleCatExtendScalarsPseudofunctor) (descentFamily f)

/-- Two morphisms of module descent data are equal when their unique components are equal. -/
theorem DescentData.hom_ext (f : R →+* S)
    {D₁ D₂ : DescentData f} {φ φ' : D₁ ⟶ D₂}
    (h : φ.hom PUnit.unit = φ'.hom PUnit.unit) :
    φ = φ' := by
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  cases i
  exact h

/-- The canonical base-extension functor from `R`-modules to descent data along
`f : R →+* S`. -/
abbrev baseExtension (f : R →+* S) :
    ModuleCat.{u} R ⥤ DescentData f :=
  Pseudofunctor.toDescentData (C := CommRingCat.{u}ᵒᵖ)
    (ι := PUnit.{1}) (S := Opposite.op (CommRingCat.of R))
    (X := fun _ ↦ Opposite.op (CommRingCat.of S))
    ((unopUnop CommRingCat.{u}).toPseudofunctor.comp
      CommRingCat.moduleCatExtendScalarsPseudofunctor) (descentFamily f)

/-- The unique object component of base extension is ordinary extension of scalars. -/
theorem baseExtension_obj_obj (f : R →+* S) (M : ModuleCat.{u} R) :
    ((baseExtension f).obj M).obj PUnit.unit = (extendScalars f).obj M := rfl

/-- The unique morphism component of base extension is ordinary extension of scalars. -/
theorem baseExtension_map_hom (f : R →+* S) {M N : ModuleCat.{u} R}
    (g : M ⟶ N) :
    ((baseExtension f).map g).hom PUnit.unit = (extendScalars f).map g := rfl

end ModuleCat

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A ring homomorphism is a descent morphism for modules when its base-extension functor is
fully faithful. -/
abbrev DescentForModules (f : R →+* S) : Prop :=
  Nonempty (ModuleCat.baseExtension f).FullyFaithful

/-- Characterization of descent morphisms for modules by full faithfulness of base
extension. -/
theorem descentForModules_iff (f : R →+* S) :
    f.DescentForModules ↔ Nonempty (ModuleCat.baseExtension f).FullyFaithful := Iff.rfl

/-- A ring homomorphism is an effective descent morphism for modules when its base-extension
functor is an equivalence of categories. -/
abbrev EffectiveDescentForModules (f : R →+* S) : Prop :=
  (ModuleCat.baseExtension f).IsEquivalence

/-- Characterization of effective descent morphisms for modules by equivalence of the
base-extension functor. -/
theorem effectiveDescentForModules_iff (f : R →+* S) :
    f.EffectiveDescentForModules ↔ (ModuleCat.baseExtension f).IsEquivalence := Iff.rfl

namespace EffectiveDescentForModules

/-- Effective descent for modules implies descent for modules. -/
theorem descent {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (h : f.EffectiveDescentForModules) :
    f.DescentForModules := by
  letI : (ModuleCat.baseExtension f).IsEquivalence := h
  exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

end EffectiveDescentForModules

end RingHom
