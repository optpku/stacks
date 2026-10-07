module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.RingTheory.Finiteness.Projective
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Continuous GL-representations over Artinian local algebras

The total category of triples `(A, M, ρ)` with `A` in `ArtinianLocalAlgCat`,
`M` a finite projective `A`-module, and a homomorphism
`ρ : Γ →* LinearMap.GeneralLinearGroup A M` that is continuous for the discrete
topology on `GL`, together with the forgetful projection to `ArtinianLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory
open Functor

universe u

variable (Γ Λ k : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]

/-- Continuity of `ρ : Γ →* LinearMap.GeneralLinearGroup R M` when `GL` is discrete,
encoded as local constancy of the underlying map. -/
def ContinuousRep.IsContinuousDiscrete {Γ R M : Type u}
    [Group Γ] [TopologicalSpace Γ] [Semiring R] [AddCommMonoid M] [Module R M]
    (ρ : Γ →* LinearMap.GeneralLinearGroup R M) : Prop :=
  IsLocallyConstant fun γ ↦ ρ γ

/-- Local constancy of a discrete-`GL` representation. -/
theorem ContinuousRep.isContinuousDiscrete_iff {Γ R M : Type u}
    [Group Γ] [TopologicalSpace Γ] [Semiring R] [AddCommMonoid M] [Module R M]
    (ρ : Γ →* LinearMap.GeneralLinearGroup R M) :
    ContinuousRep.IsContinuousDiscrete ρ ↔ IsLocallyConstant fun γ ↦ ρ γ := sorry

/-- A finite projective `A`-module with a discrete-continuous `GL`-valued action of a
topological group `Γ`, for `A` an Artinian local `Λ`-algebra with residue identification
to `k`. -/
structure ContinuousRep where
  /-- Underlying object of `ArtinianLocalAlgCat Λ k`. -/
  base : ArtinianLocalAlgCat Λ k
  /-- Underlying module. -/
  module : Type u
  [addCommGroup : AddCommGroup module]
  [isModule : Module base.carrier module]
  /-- The module is finite projective over the base algebra. -/
  finiteProjective : Module.FiniteProjective base.carrier module
  /-- The homomorphism `Γ →* LinearMap.GeneralLinearGroup` of the triple. -/
  ρ : Γ →* LinearMap.GeneralLinearGroup base.carrier module
  /-- Continuity of `ρ` for the discrete topology on `GL`. -/
  continuous_ρ : ContinuousRep.IsContinuousDiscrete ρ

attribute [instance] ContinuousRep.addCommGroup ContinuousRep.isModule

namespace ContinuousRep

variable {Γ Λ k}

/-- Bundle a finite projective module with a discrete-continuous `GL`-valued `Γ`-action
over an object of `ArtinianLocalAlgCat`. -/
def of (A : ArtinianLocalAlgCat Λ k) (M : Type u) [AddCommGroup M] [Module A.carrier M]
    (hM : Module.FiniteProjective A.carrier M)
    (ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M)
    (hρ : IsContinuousDiscrete ρ) : ContinuousRep Γ Λ k where
  base := A
  module := M
  finiteProjective := hM
  ρ := ρ
  continuous_ρ := hρ

/-- The bundled object recovers the supplied Artinian base. -/
theorem of_base (A : ArtinianLocalAlgCat Λ k) (M : Type u)
    [AddCommGroup M] [Module A.carrier M]
    (hM : Module.FiniteProjective A.carrier M)
    (ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M)
    (hρ : IsContinuousDiscrete ρ) :
    (of A M hM ρ hρ).base = A := sorry

/-- The bundled object recovers the supplied module. -/
theorem of_module (A : ArtinianLocalAlgCat Λ k) (M : Type u)
    [AddCommGroup M] [Module A.carrier M]
    (hM : Module.FiniteProjective A.carrier M)
    (ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M)
    (hρ : IsContinuousDiscrete ρ) :
    (of A M hM ρ hρ).module = M := sorry

/-- The bundled object recovers the supplied representation. -/
theorem of_ρ (A : ArtinianLocalAlgCat Λ k) (M : Type u)
    [AddCommGroup M] [Module A.carrier M]
    (hM : Module.FiniteProjective A.carrier M)
    (ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M)
    (hρ : IsContinuousDiscrete ρ) :
    (of A M hM ρ hρ).ρ = ρ := sorry

/-- Finite generation of the underlying module. -/
instance instModuleFinite (X : ContinuousRep Γ Λ k) :
    Module.Finite X.base.carrier X.module :=
  Module.FiniteProjective.finite X.finiteProjective

/-- Projectivity of the underlying module. -/
instance instModuleProjective (X : ContinuousRep Γ Λ k) :
    Module.Projective X.base.carrier X.module :=
  Module.FiniteProjective.projective X.finiteProjective

noncomputable section

/-- The `f`-linear map `g : N → M` as an unbundled linear map into restriction of scalars. -/
def restrictAlongHom {X Y : ContinuousRep Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module), g (a • m) = f.hom a • g m) :
    X.module →ₗ[X.base.carrier]
      ((ModuleCat.restrictScalars f.hom.toRingHom).obj
        (ModuleCat.of Y.base.carrier Y.module)) where
  toFun := g
  map_add' := map_add
  map_smul' := sorry

/-- The `f`-linear map `g : N → M` as a morphism into restriction of scalars along `f`. -/
def restrictAlong {X Y : ContinuousRep Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module), g (a • m) = f.hom a • g m) :
    ModuleCat.of X.base.carrier X.module ⟶
      (ModuleCat.restrictScalars f.hom.toRingHom).obj
        (ModuleCat.of Y.base.carrier Y.module) :=
  ConcreteCategory.ofHom (restrictAlongHom f g map_add map_smul)

/-- The adjunct of `restrictAlong`, witnessing the induced map `A ⊗[B, f] N ⟶ M`. -/
def inducedAlong {X Y : ContinuousRep Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module), g (a • m) = f.hom a • g m) :
    (ModuleCat.extendScalars f.hom.toRingHom).obj
      (ModuleCat.of X.base.carrier X.module) ⟶
      ModuleCat.of Y.base.carrier Y.module :=
  ((ModuleCat.extendRestrictScalarsAdj f.hom.toRingHom).homEquiv
      (ModuleCat.of X.base.carrier X.module)
      (ModuleCat.of Y.base.carrier Y.module)).symm
    (restrictAlong f g map_add map_smul)

/-- The map `g : N → M` induces the canonical identification `N ⊗[B, f] A ≅ M`. -/
def IsBaseChangeAlong {X Y : ContinuousRep Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module), g (a • m) = f.hom a • g m) :
    Prop :=
  IsIso (inducedAlong f g map_add map_smul)

/-- `IsBaseChangeAlong` means the canonical adjunct `A ⊗[B, f] N ⟶ M` is an isomorphism. -/
theorem isBaseChangeAlong_spec {X Y : ContinuousRep Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module), g (a • m) = f.hom a • g m) :
    IsBaseChangeAlong f g map_add map_smul ↔
      IsIso (inducedAlong f g map_add map_smul) := sorry

/-- A morphism of triples is a base arrow `f` together with an `f`-linear
`Γ`-equivariant map inducing the canonical isomorphism `N ⊗[B, f] A ≅ M`. -/
structure Hom (X Y : ContinuousRep Γ Λ k) where
  /-- Underlying morphism of Artinian local algebras. -/
  base : X.base ⟶ Y.base
  /-- Underlying map of modules. -/
  toFun : X.module → Y.module
  /-- Additivity of `toFun`. -/
  map_add : ∀ m₁ m₂, toFun (m₁ + m₂) = toFun m₁ + toFun m₂
  /-- `f`-linearity of `toFun`. -/
  map_smul : ∀ (a : X.base.carrier) (m : X.module),
    toFun (a • m) = base.hom a • toFun m
  /-- `Γ`-equivariance of `toFun`. -/
  map_equivariant : ∀ (γ : Γ) (n : X.module),
    toFun ((X.ρ γ).val n) = (Y.ρ γ).val (toFun n)
  /-- The induced map `A ⊗[B, f] N ⟶ M` is an isomorphism. -/
  isBaseChange : IsBaseChangeAlong base toFun map_add map_smul

namespace Hom

/-- Package a base morphism and an `f`-linear `Γ`-equivariant map inducing the
canonical base-change isomorphism. -/
def of {X Y : ContinuousRep Γ Λ k} (base : X.base ⟶ Y.base)
    (toFun : X.module → Y.module)
    (map_add : ∀ m₁ m₂, toFun (m₁ + m₂) = toFun m₁ + toFun m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module),
      toFun (a • m) = base.hom a • toFun m)
    (map_equivariant : ∀ (γ : Γ) (n : X.module),
      toFun ((X.ρ γ).val n) = (Y.ρ γ).val (toFun n))
    (isBaseChange : IsBaseChangeAlong base toFun map_add map_smul) : Hom X Y where
  base := base
  toFun := toFun
  map_add := map_add
  map_smul := map_smul
  map_equivariant := map_equivariant
  isBaseChange := isBaseChange

/-- Identity morphism of a triple. -/
def id (X : ContinuousRep Γ Λ k) : Hom X X where
  base := 𝟙 X.base
  toFun := fun m ↦ m
  map_add := sorry
  map_smul := sorry
  map_equivariant := sorry
  isBaseChange := sorry

/-- Composition of morphisms of triples. -/
def comp {X Y Z : ContinuousRep Γ Λ k} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  toFun := Function.comp g.toFun f.toFun
  map_add := sorry
  map_smul := sorry
  map_equivariant := sorry
  isBaseChange := sorry

/-- The identity morphism has identity base arrow. -/
theorem id_base (X : ContinuousRep Γ Λ k) : (id X).base = 𝟙 X.base := sorry

/-- Composition of morphisms has composed base arrows. -/
theorem comp_base {X Y Z : ContinuousRep Γ Λ k} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).base = f.base ≫ g.base := sorry

/-- Pointwise `Γ`-equivariance of a morphism of triples. -/
theorem equivariant_apply {X Y : ContinuousRep Γ Λ k} (f : Hom X Y)
    (γ : Γ) (n : X.module) :
    f.toFun ((X.ρ γ).val n) = (Y.ρ γ).val (f.toFun n) := sorry

/-- The module map of a morphism induces the canonical base-change isomorphism. -/
theorem isBaseChangeAlong_spec {X Y : ContinuousRep Γ Λ k} (f : Hom X Y) :
    IsBaseChangeAlong f.base f.toFun f.map_add f.map_smul := sorry

end Hom

/-- Category of discrete-continuous finite projective representations of `Γ`
over objects of `ArtinianLocalAlgCat Λ k`. -/
instance category : Category.{u} (ContinuousRep Γ Λ k) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end

section Forget

variable (Γ Λ k)

/-- The functor `p` sending `(A, M, ρ)` to `A` and `(f, g)` to `f`. -/
def forget : ContinuousRep Γ Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj X := X.base
  map f := f.base
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor evaluates to the stored base algebra. -/
theorem forget_obj (X : ContinuousRep Γ Λ k) : (forget Γ Λ k).obj X = X.base := sorry

/-- The forgetful functor sends a morphism to its base arrow. -/
theorem forget_map {X Y : ContinuousRep Γ Λ k} (f : X ⟶ Y) :
    (forget Γ Λ k).map f = f.base := sorry

/-- The projection `p : ContinuousRep ⥤ ArtinianLocalAlgCat` is cofibered in groupoids. -/
instance instIsCofiberedInGroupoids :
    Functor.IsFibered.InGroupoids (forget Γ Λ k).op := sorry

end Forget

end ContinuousRep
