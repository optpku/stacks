/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocallyConstant.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.RingTheory.Finiteness.Projective
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue

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
def ContinuousRep :=
  Σ' base : ArtinianLocalAlgCat Λ k,
    Σ' module : ModuleCat base.carrier,
      Σ' finiteProjective : Module.FiniteProjective base.carrier module,
        Σ' ρ : Γ →* LinearMap.GeneralLinearGroup base.carrier module,
          ContinuousRep.IsContinuousDiscrete ρ

namespace ContinuousRep

variable {Γ Λ k}

/-- The underlying object of `ArtinianLocalAlgCat Λ k` in a representation. -/
def base (X : ContinuousRep Γ Λ k) : ArtinianLocalAlgCat Λ k := X.1

/-- The underlying bundled module in a representation. -/
def module (X : ContinuousRep Γ Λ k) : ModuleCat X.base.carrier := X.2.1

/-- The stored finite-projectivity proof of a representation module. -/
def finiteProjective (X : ContinuousRep Γ Λ k) :
    Module.FiniteProjective X.base.carrier X.module := X.2.2.1

/-- The stored `Γ`-valued general-linear representation. -/
def ρ (X : ContinuousRep Γ Λ k) :
    Γ →* LinearMap.GeneralLinearGroup X.base.carrier X.module := X.2.2.2.1

/-- The stored continuity proof for the discrete general-linear representation. -/
def continuous_ρ (X : ContinuousRep Γ Λ k) : IsContinuousDiscrete X.ρ := X.2.2.2.2

/-- Bundle a finite projective module with a discrete-continuous `GL`-valued `Γ`-action
over an object of `ArtinianLocalAlgCat`. -/
def of (A : ArtinianLocalAlgCat Λ k) (M : ModuleCat A.carrier)
    (hM : Module.FiniteProjective A.carrier M)
    (ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M)
    (hρ : IsContinuousDiscrete ρ) : ContinuousRep Γ Λ k := ⟨A, M, hM, ρ, hρ⟩

/-- The bundled object recovers the supplied Artinian base. -/
theorem of_base (A : ArtinianLocalAlgCat Λ k) (M : ModuleCat A.carrier)
    (hM : Module.FiniteProjective A.carrier M)
    (ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M)
    (hρ : IsContinuousDiscrete ρ) :
    (of A M hM ρ hρ).base = A := sorry

/-- The bundled object recovers the supplied module. -/
theorem of_module (A : ArtinianLocalAlgCat Λ k) (M : ModuleCat A.carrier)
    (hM : Module.FiniteProjective A.carrier M)
    (ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M)
    (hρ : IsContinuousDiscrete ρ) :
    (of A M hM ρ hρ).module = M := sorry

/-- The bundled object recovers the supplied representation. -/
theorem of_ρ (A : ArtinianLocalAlgCat Λ k) (M : ModuleCat A.carrier)
    (hM : Module.FiniteProjective A.carrier M)
    (ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M)
    (hρ : IsContinuousDiscrete ρ) :
    (of A M hM ρ hρ).ρ = ρ := sorry

/-- Finite generation of the underlying module. -/
@[reducible]
def moduleFinite (X : ContinuousRep Γ Λ k) :
    Module.Finite X.base.carrier X.module :=
  Module.FiniteProjective.finite X.finiteProjective

/-- Projectivity of the underlying module. -/
@[reducible]
def moduleProjective (X : ContinuousRep Γ Λ k) :
    Module.Projective X.base.carrier X.module :=
  Module.FiniteProjective.projective X.finiteProjective

noncomputable section

/-- The `f`-linear map `g : N → M` as a morphism into restriction of scalars along `f`. -/
def restrictAlong {X Y : ContinuousRep Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module), g (a • m) = ArtinianLocalAlgCat.Hom.toRingHom f a • g m) :
    X.module ⟶ (ModuleCat.restrictScalars (ArtinianLocalAlgCat.Hom.toRingHom f)).obj Y.module :=
  (ModuleCat.semilinearMapAddEquiv (ArtinianLocalAlgCat.Hom.toRingHom f)
      X.module Y.module)
    { toFun := g
      map_add' := map_add
      map_smul' := map_smul }

/-- The adjunct of `restrictAlong`, witnessing the induced map `A ⊗[B, f] N ⟶ M`. -/
def inducedAlong {X Y : ContinuousRep Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module), g (a • m) = ArtinianLocalAlgCat.Hom.toRingHom f a • g m) :
    (ModuleCat.extendScalars (ArtinianLocalAlgCat.Hom.toRingHom f)).obj X.module ⟶ Y.module :=
  ((ModuleCat.extendRestrictScalarsAdj (ArtinianLocalAlgCat.Hom.toRingHom f)).homEquiv
      X.module Y.module).symm
    (restrictAlong f g map_add map_smul)

/-- The map `g : N → M` induces the canonical identification `N ⊗[B, f] A ≅ M`. -/
def IsBaseChangeAlong {X Y : ContinuousRep Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module), g (a • m) = ArtinianLocalAlgCat.Hom.toRingHom f a • g m) :
    Prop :=
  IsIso (inducedAlong f g map_add map_smul)

/-- `IsBaseChangeAlong` means the canonical adjunct `A ⊗[B, f] N ⟶ M` is an isomorphism. -/
theorem isBaseChangeAlong_spec {X Y : ContinuousRep Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module), g (a • m) = ArtinianLocalAlgCat.Hom.toRingHom f a • g m) :
    IsBaseChangeAlong f g map_add map_smul ↔
      IsIso (inducedAlong f g map_add map_smul) := sorry

/-- A morphism of triples is a base arrow `f` together with an `f`-linear
`Γ`-equivariant map inducing the canonical isomorphism `N ⊗[B, f] A ≅ M`. -/
def Hom (X Y : ContinuousRep Γ Λ k) :=
  Σ' base : X.base ⟶ Y.base,
    Σ' toFun : X.module → Y.module,
      Σ' map_add : ∀ m₁ m₂, toFun (m₁ + m₂) = toFun m₁ + toFun m₂,
        Σ' map_smul : ∀ (a : X.base.carrier) (m : X.module),
          toFun (a • m) = ArtinianLocalAlgCat.Hom.toRingHom base a • toFun m,
          Σ' map_equivariant : ∀ (γ : Γ) (n : X.module),
            toFun ((X.ρ γ).val n) = (Y.ρ γ).val (toFun n),
            IsBaseChangeAlong base toFun map_add map_smul

namespace Hom

/-- The underlying arrow of Artinian local algebras of a representation morphism. -/
def base {X Y : ContinuousRep Γ Λ k} : Hom X Y → (X.base ⟶ Y.base)
  | f => f.1

/-- The underlying module map of a representation morphism. -/
def toFun {X Y : ContinuousRep Γ Λ k} : Hom X Y → (X.module → Y.module)
  | f => f.2.1

/-- The underlying module map of a representation morphism is additive. -/
def map_add {X Y : ContinuousRep Γ Λ k} (f : Hom X Y) :
    ∀ m₁ m₂, f.toFun (m₁ + m₂) = f.toFun m₁ + f.toFun m₂ :=
  f.2.2.1

/-- The underlying module map is semilinear over the stored base arrow. -/
def map_smul {X Y : ContinuousRep Γ Λ k} (f : Hom X Y) :
    ∀ (a : X.base.carrier) (m : X.module),
      f.toFun (a • m) = ArtinianLocalAlgCat.Hom.toRingHom f.base a • f.toFun m :=
  f.2.2.2.1

/-- The underlying module map intertwines the two group actions. -/
def map_equivariant {X Y : ContinuousRep Γ Λ k} (f : Hom X Y) :
    ∀ (γ : Γ) (n : X.module), f.toFun ((X.ρ γ).val n) = (Y.ρ γ).val (f.toFun n) :=
  f.2.2.2.2.1

/-- A representation morphism induces an isomorphism after extension of scalars. -/
def isBaseChange {X Y : ContinuousRep Γ Λ k} (f : Hom X Y) :
    IsBaseChangeAlong f.base f.toFun f.map_add f.map_smul :=
  f.2.2.2.2.2

/-- Package a base morphism and an `f`-linear `Γ`-equivariant map inducing the
canonical base-change isomorphism. -/
def of {X Y : ContinuousRep Γ Λ k} (base : X.base ⟶ Y.base)
    (toFun : X.module → Y.module)
    (map_add : ∀ m₁ m₂, toFun (m₁ + m₂) = toFun m₁ + toFun m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module),
      toFun (a • m) = ArtinianLocalAlgCat.Hom.toRingHom base a • toFun m)
    (map_equivariant : ∀ (γ : Γ) (n : X.module),
      toFun ((X.ρ γ).val n) = (Y.ρ γ).val (toFun n))
    (isBaseChange : IsBaseChangeAlong base toFun map_add map_smul) : Hom X Y :=
  ⟨base, toFun, map_add, map_smul, map_equivariant, isBaseChange⟩

/-- Identity morphism of a triple. -/
def id (X : ContinuousRep Γ Λ k) : Hom X X :=
  of (𝟙 X.base) (fun m ↦ m) sorry sorry sorry sorry

/-- Composition of morphisms of triples. -/
def comp {X Y Z : ContinuousRep Γ Λ k} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  of (f.base ≫ g.base) (Function.comp g.toFun f.toFun) sorry sorry sorry sorry

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

section Residue

variable (Γ Λ k)

/-- A `k`-module is a module over the residue object of `ArtinianLocalAlgCat`. -/
instance instModuleResidueCarrier {V : Type u} [AddCommGroup V] [Module k V] :
    Module (ArtinianLocalAlgCat.residue Λ k).carrier V :=
  inferInstanceAs (Module k V)

/-- The residue object associated to a finite-dimensional continuous representation. -/
def ofResidue {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    ContinuousRep Γ Λ k :=
  of (ArtinianLocalAlgCat.residue Λ k)
    (ModuleCat.of (ArtinianLocalAlgCat.residue Λ k).carrier V) sorry ρ0 hρ0

/-- The projection of a residue representation is the residue base object. -/
theorem ofResidue_base {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) (hρ0 : IsContinuousDiscrete ρ0) :
    (forget Γ Λ k).obj (ofResidue Γ Λ k ρ0 hρ0) = ArtinianLocalAlgCat.residue Λ k := sorry

/-- The deformation category of a residue representation is its Over category. -/
abbrev deformationCategory {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :=
  Over (ofResidue Γ Λ k ρ0 hρ0)

/-- The deformation category is the Over category at the residue representation. -/
theorem deformationCategory_spec {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V)
    (hρ0 : IsContinuousDiscrete ρ0) :
    deformationCategory Γ Λ k ρ0 hρ0 = Over (ofResidue Γ Λ k ρ0 hρ0) := sorry

end Residue

end ContinuousRep
