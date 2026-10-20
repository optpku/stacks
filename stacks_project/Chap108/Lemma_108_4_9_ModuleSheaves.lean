/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! Proved module-sheaf certificates; no admitted ReasLib instances are imported. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site

variable {C : Type v} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Filtered colimits of varying-ring module presheaves are exact. -/
theorem presheafAB5 : AB5OfSize.{u, u} (PresheafOfModules.{u} R.obj) where
  ofShape I _ _ := HasExactColimitsOfShape.domain_of_functor I
    (PresheafOfModules.toPresheaf R.obj)

/-- Exact module sheafification transports exact filtered colimits. -/
theorem sheafAB5 : AB5OfSize.{u, u} (SheafOfModules.{u} R) := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := presheafAB5 J R
  exact ⟨fun I _ _ ↦ (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape I⟩

/-- The free module sheaf on the representable of a site object. -/
noncomputable def freeAt (X : C) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj X))

/-- The free sheaf at each object detects morphisms of module sheaves. -/
theorem freeAtSeparating : ObjectProperty.IsSeparating (.ofObj (freeAt J R)) := by
  intro M N f g h
  apply (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map_injective
  apply PresheafOfModules.freeYoneda.isSeparating R.obj
  rintro _ ⟨X⟩ a
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).symm.injective
  rw [(PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_right_symm a f,
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_right_symm a g]
  exact h _ (ObjectProperty.ofObj_apply _ X)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).symm a)

section SmallSite

variable {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
  (O : Sheaf K RingCat.{u})
  [HasSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- An explicit generator: the coproduct of sheafified free representables. -/
noncomputable def generator : SheafOfModules.{u} O := ∐ (freeAt K O)

/-- The specified generator is separating. -/
theorem generatorSeparates : IsSeparator (generator K O) :=
  (freeAtSeparating K O).isSeparator_coproduct

/-- A proved Grothendieck certificate for modules over a varying ring on a small site. -/
theorem modulesGrothendieck : IsGrothendieckAbelian.{u} (SheafOfModules.{u} O) := by
  -- Local instance justification (proof-local temporary data): Pin the proved small-basis/site certificate for this construction; do not synthesize a legacy admitted witness.
  letI := sheafAB5 K O
  exact { hasSeparator := ⟨generator K O, generatorSeparates K O⟩ }

end SmallSite

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.TensorPower.Site
