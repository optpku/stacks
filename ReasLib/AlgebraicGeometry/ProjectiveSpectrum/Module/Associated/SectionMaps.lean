/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bundled section maps for associated graded modules

This module packages the canonical degree-zero and standard-open section maps as morphisms in
`ModuleCat`.  The underlying linear maps remain owned by `AssociatedModule`; this leaf supplies
the categorical interface needed by comparison squares.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u v w

namespace AlgebraicGeometry.Proj.AssociatedModule

variable {R : Type u} {A M : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [Module A M]
variable {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]

/-- The degree-zero map to global associated sections, bundled as a morphism after restriction
of scalars along `degreeZeroRingHom`. -/
@[stacks 01MK "bundled degree-zero associated-section map"]
noncomputable def degreeZeroToGlobalSectionsHom :
    ModuleCat.of (𝒜 0) (ℳ 0) ⟶
      (ModuleCat.restrictScalars (degreeZeroRingHom 𝒜)).obj
        (sectionModule 𝒜 ℳ ⊤) :=
  ModuleCat.ofHom
    (X := ModuleCat.of (𝒜 0) (ℳ 0))
    (Y := (ModuleCat.restrictScalars (degreeZeroRingHom 𝒜)).obj
      (sectionModule 𝒜 ℳ ⊤))
    (degreeZeroToGlobalSections 𝒜 ℳ)

/-- The bundled degree-zero section morphism evaluates to the canonical global section. -/
@[simp]
theorem degreeZeroToGlobalSectionsHom_apply (m : ℳ 0) :
    degreeZeroToGlobalSectionsHom 𝒜 ℳ m = degreeZeroSection 𝒜 ℳ m := sorry

/-- The standard-open fraction map, bundled as a morphism after scalar transport through
`Proj.basicOpenIsoAway`. -/
@[stacks 01MK "bundled standard-open associated-section map"]
noncomputable def awaySectionHom {d : ℕ} (f : 𝒜 d) (hd : 0 < d) :
    ModuleCat.of (HomogeneousLocalization.Away 𝒜 (f : A)) (away 𝒜 ℳ f) ⟶
      (ModuleCat.restrictScalars
        (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
          (sectionModule 𝒜 ℳ (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))) :=
  ModuleCat.ofHom
    (X := ModuleCat.of (HomogeneousLocalization.Away 𝒜 (f : A)) (away 𝒜 ℳ f))
    (Y := (ModuleCat.restrictScalars
      (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 (f : A) f.2 hd).hom.hom).obj
        (sectionModule 𝒜 ℳ (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A))))
    (awaySectionLinearMap 𝒜 ℳ f hd)

/-- The bundled standard-open section morphism evaluates to the canonical fraction section. -/
@[simp]
theorem awaySectionHom_apply {d : ℕ} (f : 𝒜 d) (hd : 0 < d)
    (z : away 𝒜 ℳ f) :
    awaySectionHom 𝒜 ℳ f hd z = awaySection 𝒜 ℳ f hd z := sorry

end AlgebraicGeometry.Proj.AssociatedModule
