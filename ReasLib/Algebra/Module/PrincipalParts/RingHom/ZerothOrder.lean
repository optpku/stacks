/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.RingHom
public import ReasLib.Algebra.Module.PrincipalParts.ZerothOrder

/-!
# Zeroth principal parts attached to an explicit ring homomorphism

This file bundles the canonical zeroth-order comparison in `ModuleCat`, keeping the chosen ring
map explicit and hiding the presentation-level scalar instances.

@stack 09CL
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace PrincipalParts.RingHom.ZerothOrder

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The bundled projection from zeroth principal parts to the original module. -/
noncomputable def projection (σ : R →+* S) (M : ModuleCat.{u} S) :
    PrincipalParts.RingHom.module σ M 0 ⟶ M :=
  -- Local instance justification (instance diamond): this projection uses the scalar structures
  -- induced by the explicit `σ`; competing maps with the same endpoints need not agree.
  letI : Algebra R S := algebra σ
  letI : Module R M := sourceModule σ M
  letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  ModuleCat.ofHom (PrincipalParts.ZerothOrder.projection (R := R) (S := S) (M := M))

/-- The bundled inverse from the original module to its zeroth principal parts. -/
noncomputable def inclusion (σ : R →+* S) (M : ModuleCat.{u} S) :
    M ⟶ PrincipalParts.RingHom.module σ M 0 :=
  -- Local instance justification (instance diamond): this inverse uses the scalar structures
  -- induced by the explicit `σ`; they are intentionally confined to the adapter.
  letI : Algebra R S := algebra σ
  letI : Module R M := sourceModule σ M
  letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  ModuleCat.ofHom (PrincipalParts.ZerothOrder.inclusion (R := R) (S := S) (M := M))

/-- Projection followed by inclusion is the identity on zeroth principal parts. -/
@[simp]
theorem projection_inclusion (σ : R →+* S) (M : ModuleCat.{u} S) :
    projection σ M ≫ inclusion σ M = 𝟙 (PrincipalParts.RingHom.module σ M 0) := sorry

/-- Inclusion followed by projection is the identity on the original module. -/
@[simp]
theorem inclusion_projection (σ : R →+* S) (M : ModuleCat.{u} S) :
    inclusion σ M ≫ projection σ M = 𝟙 M := sorry

/-- Zeroth principal parts are canonically isomorphic to the original bundled module. -/
@[stacks 09CL "explicit ring-hom zeroth principal parts"]
noncomputable def iso (σ : R →+* S) (M : ModuleCat.{u} S) :
    PrincipalParts.RingHom.module σ M 0 ≅ M :=
  CategoryTheory.Iso.mk (projection σ M) (inclusion σ M)
    (projection_inclusion σ M) (inclusion_projection σ M)

/-- The zeroth projection is natural in the bundled module. -/
theorem projection_naturality (σ : R →+* S) {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    PrincipalParts.RingHom.map σ 0 f ≫ projection σ N = projection σ M ≫ f := sorry

/-- The inverse zeroth comparison is natural in the bundled module. -/
@[stacks 09CL "inverse zeroth principal-parts naturality"]
theorem inclusion_naturality (σ : R →+* S) {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    f ≫ inclusion σ N = inclusion σ M ≫ PrincipalParts.RingHom.map σ 0 f := sorry

/-- Zeroth principal parts are naturally isomorphic to the identity endofunctor on bundled
modules. -/
@[stacks 09CL "explicit ring-hom zeroth principal-parts natural isomorphism"]
noncomputable def natIso (σ : R →+* S) :
    PrincipalParts.RingHom.functor σ 0 ≅ 𝟭 (ModuleCat.{u} S) :=
  NatIso.ofComponents (fun M ↦ iso σ M) (projection_naturality σ)

/-- A component of `natIso` is the objectwise zeroth principal-parts isomorphism. -/
@[simp, stacks 09CL "zeroth principal-parts natural isomorphism component"]
theorem natIso_app (σ : R →+* S) (M : ModuleCat.{u} S) :
    (natIso σ).app M = iso σ M :=
  NatIso.ofComponents.app _ _ _

/-- The forward component of `natIso` is `projection`. -/
@[simp, stacks 09CL "zeroth principal-parts natural isomorphism hom component"]
theorem natIso_hom_app (σ : R →+* S) (M : ModuleCat.{u} S) :
    (natIso σ).hom.app M = projection σ M := rfl

/-- The inverse component of `natIso` is `inclusion`. -/
@[simp, stacks 09CL "zeroth principal-parts natural isomorphism inverse component"]
theorem natIso_inv_app (σ : R →+* S) (M : ModuleCat.{u} S) :
    (natIso σ).inv.app M = inclusion σ M := rfl

end PrincipalParts.RingHom.ZerothOrder

end
