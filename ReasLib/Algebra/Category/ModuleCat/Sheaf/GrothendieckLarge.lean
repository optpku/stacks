/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace PresheafOfModules.LargeSite

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{max u v})

/-- The free module presheaf on the actual universe-lifted representable. -/
noncomputable def freeRepresentable (X : C) : PresheafOfModules.{max u v} R :=
  (PresheafOfModules.free R).obj (uliftYoneda.{u}.obj X)

/-- Evaluation of a free represented module map at the identity generator. -/
noncomputable def evaluation {M : PresheafOfModules.{max u v} R} {X : C} :
    (freeRepresentable R X ⟶ M) ≃ M.obj (op X) :=
  PresheafOfModules.freeHomEquiv.trans uliftYonedaEquiv.{u}

/-- Evaluation commutes with a specified module-presheaf morphism. -/
theorem evaluation_comp {M N : PresheafOfModules.{max u v} R} {X : C}
    (f : freeRepresentable R X ⟶ M) (g : M ⟶ N) :
    evaluation R (f ≫ g) = g.app _ (evaluation R f) := rfl

/-- Free modules on all actual represented presheaves separate maps. -/
theorem freeRepresentable_isSeparating :
    ObjectProperty.IsSeparating (.ofObj (freeRepresentable R)) := by
  intro M N f g h
  ext ⟨X⟩ m
  obtain ⟨a, rfl⟩ := (evaluation R).surjective m
  exact congrArg (evaluation R) (h _ ⟨X⟩ a)

/-- The index of the explicit generator lies in the enlarged module universe. -/
noncomputable def generator : PresheafOfModules.{max u v} R :=
  ∐ freeRepresentable R

/-- The explicit free-representable coproduct is a separator. -/
theorem generator_isSeparator : IsSeparator (generator R) :=
  (freeRepresentable_isSeparating R).isSeparator_coproduct

/-- Filtered colimits are exact after forgetting the variable ring action. -/
theorem ab5 : AB5OfSize.{max u v, max u v} (PresheafOfModules.{max u v} R) := by
  -- Local instance justification (proof-local temporary data): reflect isomorphisms only for this variable-ring forgetful functor.
  letI : (PresheafOfModules.toPresheaf R).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms _
  -- Local instance justification (proof-local temporary data): transfer the finite-limit part of this exactness argument through the specified forgetful functor.
  letI : ReflectsFiniteLimits (PresheafOfModules.toPresheaf R) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms _
  exact ⟨fun J _ _ ↦ HasExactColimitsOfShape.domain_of_functor J
    (PresheafOfModules.toPresheaf R)⟩

/-- Modules in a universe containing the site's objects are Grothendieck abelian. -/
theorem grothendieck :
    IsGrothendieckAbelian.{max u v} (PresheafOfModules.{max u v} R) where
  ab5OfSize := ab5 R
  hasSeparator := ⟨generator R, generator_isSeparator R⟩

/-- The proved generator and exactness yield actual injective presentations. -/
theorem enoughInjectives : EnoughInjectives (PresheafOfModules.{max u v} R) := by
  -- Local instance justification (proof-local temporary data): use the proved generator certificate at the actual variable ring R.
  letI := grothendieck R
  infer_instance

end PresheafOfModules.LargeSite

namespace SheafOfModules.LargeSite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{max u v})

/-- Sheafification of the displayed free-representable generator. -/
noncomputable def generator : SheafOfModules.{max u v} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    (PresheafOfModules.LargeSite.generator R.obj)

/-- The actual sheafification adjunction preserves the displayed separating object. -/
theorem generator_isSeparator : IsSeparator (generator J R) := by
  rw [isSeparator_def]
  intro M N f g h
  apply (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map_injective
  apply (PresheafOfModules.LargeSite.generator_isSeparator R.obj).def
  intro t
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have e := congrArg (adj.homEquiv _ N) (h ((adj.homEquiv _ M).symm t))
  have ef := adj.homEquiv_naturality_right ((adj.homEquiv _ M).symm t) f
  have eg := adj.homEquiv_naturality_right ((adj.homEquiv _ M).symm t) g
  simpa only [Equiv.apply_symm_apply] using ef.symm.trans (e.trans eg)

/-- Module sheafification transfers exact filtered colimits. -/
theorem ab5 : AB5OfSize.{max u v, max u v} (SheafOfModules.{max u v} R) := by
  -- Local instance justification (proof-local temporary data): the sheafification argument uses exact filtered colimits of these module presheaves.
  letI := PresheafOfModules.LargeSite.ab5 R.obj
  exact ⟨fun K _ _ ↦
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K⟩

/-- The module universe contains the object index; no smallness axiom is used. -/
theorem grothendieck : IsGrothendieckAbelian.{max u v} (SheafOfModules.{max u v} R) where
  ab5OfSize := ab5 J R
  hasSeparator := ⟨generator J R, generator_isSeparator J R⟩

/-- Honest enlarged-universe variable-ring sheaves have enough injectives. -/
theorem enoughInjectives : EnoughInjectives (SheafOfModules.{max u v} R) := by
  -- Local instance justification (proof-local temporary data): use this site's proved generator and exact filtered colimits to construct injectives.
  letI := grothendieck J R
  infer_instance

/-- The proved injective presentations enable Mathlib's resolution construction. -/
@[instance]
theorem injectiveResolutions : HasInjectiveResolutions (SheafOfModules.{max u v} R) := by
  -- Local instance justification (proof-local temporary data): supply the proved injective presentations to the resolution construction at this site.
  letI := enoughInjectives J R
  infer_instance

end SheafOfModules.LargeSite
