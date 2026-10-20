/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Linear.Yoneda
public import ReasLib.Algebra.Category.ModuleCat.DifferentialOperator
public import ReasLib.Algebra.Module.PrincipalParts.Functorial
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal parts attached to an explicit ring homomorphism

The presentation-level principal-parts API is expressed using typeclass-supplied algebra and
module structures.  This file gives its reusable categorical interface: the ring map is an
explicit argument, modules are bundled in `ModuleCat`, and all scalar-action choices are confined
to this adapter.  Presheaf and sheaf constructions should use this interface rather than rebuild
the same noncanonical scalar towers objectwise.

@stack 09CK
@stack 09CL
@stack 09CN
-/

public section

open CategoryTheory

universe u

noncomputable section

namespace PrincipalParts.RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The canonical algebra structure selected by an explicit ring homomorphism.

This is a named support owner for the RingHom adapter.  It is deliberately not a global
instance: the endpoint rings alone do not determine which map `R →+* S` supplies the scalar
action. -/
@[expose, reducible, stacks 09CL "ring-hom algebra support"]
noncomputable def algebra (σ : R →+* S) : Algebra R S := σ.toAlgebra

/-- The source-ring module structure on a bundled target-ring module selected by `σ`. -/
@[expose, reducible, stacks 09CL "ring-hom module support"]
noncomputable def sourceModule (σ : R →+* S) (M : ModuleCat.{u} S) : Module R M :=
  Module.compHom M σ

/-- The `k`-th principal-parts module attached to an explicit ring homomorphism `σ : R →+* S`. -/
@[stacks 09CL "explicit ring-hom module"]
abbrev module (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ) : ModuleCat.{u} S :=
  -- Local instance justification (instance diamond): `σ` determines this algebra and its
  -- restricted module action, while another map with the same endpoints need not agree.
  letI : Algebra R S := algebra σ
  letI : Module R M := sourceModule σ M
  letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  ModuleCat.of S (PrincipalParts.module R S M k)

/-- The universal class of an element in principal parts attached to an explicit ring map. -/
abbrev universalClass (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ) (m : M) :
    module σ M k :=
  -- Local instance justification (instance diamond): the explicit map `σ` is the unique scalar
  -- choice for this adapter call, but it is not coherent across all maps `R →+* S`.
  letI : Algebra R S := algebra σ
  letI : Module R M := sourceModule σ M
  letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  PrincipalParts.universalDifferential (R := R) (S := S) (M := M) k m

/-- The universal differential as a morphism after restricting scalars along the explicit ring
map. -/
noncomputable def universalDifferential (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ) :
    (ModuleCat.restrictScalars σ).obj M ⟶
      (ModuleCat.restrictScalars σ).obj (module σ M k) :=
  -- Local instance justification (instance diamond): the typeclass-based presentation is
  -- specialized to the explicitly supplied map `σ` only inside this construction.
  letI : Algebra R S := algebra σ
  letI : Module R M := sourceModule σ M
  letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  ModuleCat.ofHom (PrincipalParts.universalDifferential (R := R) (S := S) (M := M) k)

/-- Order-`k` differential operators between bundled `S`-modules, relative to the explicit map
`σ : R →+* S`. -/
abbrev operators (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ)
    (N : ModuleCat.{u} S) :=
  ModuleCat.DifferentialOperators.ofOrder σ M k N

/-- The representing equivalence for principal parts as an `S`-linear equivalence.  It is the
composite of the canonical principal-parts equivalence with the bundled/unbundled operator
comparison. -/
@[stacks 09CK "linear representing equivalence"]
noncomputable def representingLinearEquiv (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ)
    (N : ModuleCat.{u} S) : (module σ M k ⟶ N) ≃ₗ[S] operators σ M k N :=
  -- Local instance justification (instance diamond): both restricted source actions must be
  -- induced by this explicit `σ`; registering them globally would conflate competing maps.
  letI : Algebra R S := algebra σ
  letI : Module R M := sourceModule σ M
  letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  letI : Module R N := sourceModule σ N
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  (ModuleCat.homLinearEquiv.trans
    (PrincipalParts.representingEquiv R S M k N)).trans
      (ModuleCat.DifferentialOperators.linearEquiv σ M k N).symm

/-- The representing equivalence for principal parts, with the ring map explicit and both modules
bundled. -/
@[stacks 09CK "explicit ring-hom representing equivalence"]
noncomputable def representingEquiv (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ)
    (N : ModuleCat.{u} S) : (module σ M k ⟶ N) ≃ operators σ M k N :=
  (representingLinearEquiv σ M k N).toEquiv

/-- The explicit-ring-hom representing equivalence is natural in the target module. -/
@[stacks 09CK "target naturality"]
theorem representingEquiv_natural (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ)
    {N P : ModuleCat.{u} S} (g : N ⟶ P) (f : module σ M k ⟶ N) :
    representingEquiv σ M k P (f ≫ g) =
      ModuleCat.DifferentialOperators.postcompose σ g (representingEquiv σ M k N f) := sorry

/-- The objectwise `ModuleCat S` isomorphism furnished by the principal-parts representing
equivalence. -/
noncomputable def representingModuleIso (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ)
    (N : ModuleCat.{u} S) :
    ModuleCat.of S (module σ M k ⟶ N) ≅
      ModuleCat.DifferentialOperators.module σ M k N :=
  (representingLinearEquiv σ M k N).toModuleIso

/-- The objectwise module isomorphisms furnished by principal parts are natural in the target. -/
private theorem representingModuleIso_naturality (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ)
    {N P : ModuleCat.{u} S} (g : N ⟶ P) :
    ((linearCoyoneda S (ModuleCat.{u} S)).obj (Opposite.op (module σ M k))).map g ≫
        (representingModuleIso σ M k P).hom =
      (representingModuleIso σ M k N).hom ≫
        (ModuleCat.DifferentialOperators.moduleFunctor σ M k).map g := sorry

/-- Principal parts represent the `ModuleCat S`-valued functor of differential operators of
bounded order. -/
@[stacks 09CK "module-valued representability"]
noncomputable def representingIso (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ) :
    (linearCoyoneda S (ModuleCat.{u} S)).obj (Opposite.op (module σ M k)) ≅
      ModuleCat.DifferentialOperators.moduleFunctor σ M k :=
  NatIso.ofComponents (fun N ↦ representingModuleIso σ M k N)
    (representingModuleIso_naturality σ M k)

/-- A component of `representingIso` is the objectwise representing module isomorphism. -/
@[simp, stacks 09CK "principal-parts representing natural isomorphism component"]
theorem representingIso_app (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ)
    (N : ModuleCat.{u} S) :
    (representingIso σ M k).app N = representingModuleIso σ M k N :=
  NatIso.ofComponents.app _ _ _

/-- Principal parts, together with their representing equivalence, corepresent the type-valued
differential-operator functor. -/
@[stacks 09CK "principal-parts corepresenting object"]
noncomputable def corepresentableBy
    (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ) :
    (ModuleCat.DifferentialOperators.moduleFunctor σ M k ⋙
      forget (ModuleCat.{u} S)).CorepresentableBy (module σ M k) :=
  Functor.corepresentableByEquiv.symm <|
    Functor.isoWhiskerRight (representingIso σ M k) (forget (ModuleCat.{u} S))

/-- The type-valued differential-operator functor is corepresentable. -/
@[stacks 09CK "principal-parts corepresentability"]
noncomputable instance moduleFunctor_isCorepresentable
    (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ) :
    (ModuleCat.DifferentialOperators.moduleFunctor σ M k ⋙
      forget (ModuleCat.{u} S)).IsCorepresentable :=
  (corepresentableBy σ M k).isCorepresentable

/-- The hom-equivalence of the corepresenting witness is the principal-parts representing
equivalence. -/
@[simp, stacks 09CK "principal-parts corepresenting hom equivalence"]
theorem corepresentableBy_homEquiv
    (σ : R →+* S) (M : ModuleCat.{u} S) (k : ℕ) (N : ModuleCat.{u} S) :
    @(corepresentableBy σ M k).homEquiv N = representingEquiv σ M k N := by
  change
    ((forget (ModuleCat.{u} S)).mapIso ((representingIso σ M k).app N)).toEquiv =
      representingEquiv σ M k N
  rw [representingIso_app]
  rfl

/-- The principal-parts morphism induced by a morphism of bundled modules over a fixed explicit
ring map. -/
@[stacks 09CN "explicit ring-hom functoriality"]
noncomputable def map (σ : R →+* S) (k : ℕ) {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    module σ M k ⟶ module σ N k :=
  -- Local instance justification (instance diamond): functoriality is specialized to the
  -- explicit ring map `σ`, whose induced actions are not globally coherent data.
  letI : Algebra R S := algebra σ
  letI : Module R M := sourceModule σ M
  letI : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  letI : Module R N := sourceModule σ N
  letI : IsScalarTower R S N := IsScalarTower.of_compHom R S N
  ModuleCat.ofHom (PrincipalParts.map (R := R) (S := S) k f.hom)

/-- The bundled principal-parts map sends universal classes to universal classes. -/
@[simp]
theorem map_universalClass (σ : R →+* S) (k : ℕ) {M N : ModuleCat.{u} S}
    (f : M ⟶ N) (m : M) :
    (map σ k f).hom (universalClass σ M k m) = universalClass σ N k (f.hom m) := sorry

/-- Principal-parts functoriality for an explicit ring map preserves identities. -/
@[simp]
theorem map_id (σ : R →+* S) (k : ℕ) (M : ModuleCat.{u} S) :
    map σ k (𝟙 M) = 𝟙 (module σ M k) := sorry

/-- Principal-parts functoriality for an explicit ring map preserves composition. -/
@[simp]
theorem map_comp (σ : R →+* S) (k : ℕ) {M N P : ModuleCat.{u} S}
    (f : M ⟶ N) (g : N ⟶ P) : map σ k (f ≫ g) = map σ k f ≫ map σ k g := sorry

/-- Principal parts of fixed order define an endofunctor on bundled modules over the target
ring. -/
@[expose, stacks 09CN "explicit ring-hom principal-parts functor"]
noncomputable def functor (σ : R →+* S) (k : ℕ) : ModuleCat.{u} S ⥤ ModuleCat.{u} S where
  obj M := module σ M k
  map f := map σ k f
  map_id M := map_id σ k M
  map_comp f g := map_comp σ k f g

namespace functor

/-- The principal-parts functor preserves addition of module morphisms. -/
instance additive (σ : R →+* S) (k : ℕ) : (functor σ k).Additive := sorry

/-- The principal-parts functor is linear over the target ring. -/
instance linear (σ : R →+* S) (k : ℕ) : Functor.Linear S (functor σ k) := sorry

end functor

end PrincipalParts.RingHom

end
