/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.InfinitesimalAutomorphisms

/-!
# Infinitesimal automorphisms of dual-number pullbacks

Typed checks preserve the cartesian section and fibre-automorphism API for existing
chapter imports.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
variable (x0 : X.p.Fiber (Over.mk kToS))
variable (x0' : X.p.Fiber (specDualNumber openImmersion k))
variable (φ : Fiber.fiberInclusion.obj x0' ⟶ Fiber.fiberInclusion.obj x0)
variable [X.p.IsHomLift (specDualNumberToResidue openImmersion k kToS h_factor) φ]
variable [X.p.IsStronglyCartesian (specDualNumberToResidue openImmersion k kToS h_factor) φ]

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.pullbackSection openImmersion kToS h_factor X x0 x0' φ :
    Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj x0')

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.pullbackSection_isHomLift openImmersion kToS h_factor X x0 x0' φ :
    X.p.IsHomLift
      (specOver_toResidue openImmersion kToS h_factor (ArtinianLocalAlgCat.dualNumber Λ k))
      (pullbackSection openImmersion kToS h_factor X x0 x0' φ))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.pullbackSection_comp openImmersion kToS h_factor X x0 x0' φ :
    pullbackSection openImmersion kToS h_factor X x0 x0' φ ≫ φ =
      𝟙 (Fiber.fiberInclusion.obj x0))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.restrictAut openImmersion kToS h_factor X x0 x0' φ :
    Aut x0' →* Aut x0)

variable (α : Aut x0')

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.restrictAut_apply openImmersion kToS h_factor X x0 x0' φ α :
    Fiber.fiberInclusion.map (restrictAut openImmersion kToS h_factor X x0 x0' φ α).hom =
      pullbackSection openImmersion kToS h_factor X x0 x0' φ ≫
        Fiber.fiberInclusion.map α.hom ≫ φ)

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.infinitesimalAutomorphisms openImmersion kToS h_factor X x0 x0' φ :
    Subgroup (Aut x0'))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.mem_infinitesimalAutomorphisms openImmersion kToS h_factor X x0 x0' φ α :
    α ∈ infinitesimalAutomorphisms openImmersion kToS h_factor X x0 x0' φ ↔
      pullbackSection openImmersion kToS h_factor X x0 x0' φ ≫
          Fiber.fiberInclusion.map α.hom =
        pullbackSection openImmersion kToS h_factor X x0 x0' φ)

end AlgebraicGeometry.GroupoidsOver.Predeformation
