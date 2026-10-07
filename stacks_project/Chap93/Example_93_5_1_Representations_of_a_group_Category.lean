module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RepresentationTheory.Basic
public import ReasLib.RingTheory.Finiteness.Projective
public import stacks_project.Chap90.Definition_90_16_8_Predeformation

/-!
# Finite projective representations over Artinian local algebras

The total category of triples `(A, M, ρ)` with `A` in `ArtinianLocalAlgCat`,
`M` a finite projective `A`-module, and `ρ : Γ →* LinearMap.GeneralLinearGroup A M`,
together with the forgetful projection to `ArtinianLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory
open Functor

universe u

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]

/-- A finite projective `A`-module with a `GL`-valued action of `Γ`, for `A` an
Artinian local `Λ`-algebra with residue identification to `k`. -/
structure GroupRepCat where
  /-- Underlying object of `ArtinianLocalAlgCat Λ k`. -/
  base : ArtinianLocalAlgCat Λ k
  /-- Underlying module. -/
  module : Type u
  [addCommGroup : AddCommGroup module]
  [isModule : Module base.carrier module]
  /-- The module is finite projective over the base algebra. -/
  finiteProjective : Module.FiniteProjective base.carrier module
  /-- The homomorphism `Γ →* LinearMap.GeneralLinearGroup` of the triple. -/
  rho : Γ →* LinearMap.GeneralLinearGroup base.carrier module

attribute [instance] GroupRepCat.addCommGroup GroupRepCat.isModule

namespace GroupRepCat

variable {Γ Λ k}

/-- Bundle a finite projective module with a `GL`-valued `Γ`-action over an
object of `ArtinianLocalAlgCat`. -/
def of (A : ArtinianLocalAlgCat Λ k) (M : Type u) [AddCommGroup M] [Module A.carrier M]
    (hM : Module.FiniteProjective A.carrier M)
    (ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M) : GroupRepCat Γ Λ k where
  base := A
  module := M
  finiteProjective := hM
  rho := ρ

/-- An object of `GroupRepCat` is a finite projective module together with a
`GL`-valued action of `Γ`. -/
theorem spec (X : GroupRepCat Γ Λ k) :
    Module.FiniteProjective X.base.carrier X.module ∧ (X.rho = X.rho) := sorry

/-- Finite generation of the underlying module. -/
instance instModuleFinite (X : GroupRepCat Γ Λ k) : Module.Finite X.base.carrier X.module :=
  Module.FiniteProjective.finite X.finiteProjective

/-- Projectivity of the underlying module. -/
instance instModuleProjective (X : GroupRepCat Γ Λ k) :
    Module.Projective X.base.carrier X.module :=
  Module.FiniteProjective.projective X.finiteProjective

/-- Restriction of scalars along the residue identification, so a `k`-module is a
module over the residue object of `ArtinianLocalAlgCat`. -/
instance instModuleResidueCarrier {V : Type u} [AddCommGroup V] [Module k V] :
    Module (ArtinianLocalAlgCat.residue Λ k).carrier V :=
  inferInstanceAs (Module k V)

noncomputable section

/-- The `f`-linear map `g : N → M` as an unbundled linear map into restriction of scalars. -/
def linearAlongHom {X Y : GroupRepCat Γ Λ k} (f : X.base ⟶ Y.base)
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
def linearAlong {X Y : GroupRepCat Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module), g (a • m) = f.hom a • g m) :
    ModuleCat.of X.base.carrier X.module ⟶
      (ModuleCat.restrictScalars f.hom.toRingHom).obj
        (ModuleCat.of Y.base.carrier Y.module) :=
  ConcreteCategory.ofHom (linearAlongHom f g map_add map_smul)

/-- The adjunct of `linearAlong`, witnessing the induced map `A ⊗[B, f] N ⟶ M`. -/
def induced {X Y : GroupRepCat Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module), g (a • m) = f.hom a • g m) :
    (ModuleCat.extendScalars f.hom.toRingHom).obj
      (ModuleCat.of X.base.carrier X.module) ⟶
      ModuleCat.of Y.base.carrier Y.module :=
  ((ModuleCat.extendRestrictScalarsAdj f.hom.toRingHom).homEquiv
      (ModuleCat.of X.base.carrier X.module)
      (ModuleCat.of Y.base.carrier Y.module)).symm
    (linearAlong f g map_add map_smul)

/-- A morphism of triples is a base arrow `f` together with an `f`-linear
`Γ`-equivariant map inducing an isomorphism after extension of scalars. -/
structure Hom (X Y : GroupRepCat Γ Λ k) where
  /-- Underlying morphism of Artinian local algebras. -/
  base : X.base ⟶ Y.base
  /-- Underlying map of modules. -/
  toFun : X.module → Y.module
  /-- Additivity of `toFun`. -/
  map_add : ∀ m₁ m₂, toFun (m₁ + m₂) = toFun m₁ + toFun m₂
  /-- `f`-linearity of `toFun`. -/
  map_smul : ∀ (a : X.base.carrier) (m : X.module), toFun (a • m) = base.hom a • toFun m
  /-- `Γ`-equivariance of `toFun`. -/
  equivariant : ∀ (γ : Γ) (m : X.module),
    toFun ((X.rho γ).val m) = (Y.rho γ).val (toFun m)
  /-- The induced map `A ⊗[B, f] N ⟶ M` is an isomorphism. -/
  inducesIso : IsIso (induced base toFun map_add map_smul)

namespace Hom

/-- Package a base morphism and an `f`-linear `Γ`-equivariant map inducing an
isomorphism after extension of scalars. -/
def of {X Y : GroupRepCat Γ Λ k} (base : X.base ⟶ Y.base) (toFun : X.module → Y.module)
    (map_add : ∀ m₁ m₂, toFun (m₁ + m₂) = toFun m₁ + toFun m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module),
      toFun (a • m) = base.hom a • toFun m)
    (equivariant : ∀ (γ : Γ) (m : X.module),
      toFun ((X.rho γ).val m) = (Y.rho γ).val (toFun m))
    (inducesIso : IsIso (induced base toFun map_add map_smul)) : Hom X Y where
  base := base
  toFun := toFun
  map_add := map_add
  map_smul := map_smul
  equivariant := equivariant
  inducesIso := inducesIso

/-- Identity morphism of a triple. -/
def id (X : GroupRepCat Γ Λ k) : Hom X X where
  base := 𝟙 X.base
  toFun := fun m ↦ m
  map_add := sorry
  map_smul := sorry
  equivariant := sorry
  inducesIso := sorry

/-- Composition of morphisms of triples. -/
def comp {X Y Z : GroupRepCat Γ Λ k} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  toFun := Function.comp g.toFun f.toFun
  map_add := sorry
  map_smul := sorry
  equivariant := sorry
  inducesIso := sorry

/-- The induced map `A ⊗[B, f] N ⟶ M` attached to a morphism of triples. -/
def induced {X Y : GroupRepCat Γ Λ k} (f : Hom X Y) :
    (ModuleCat.extendScalars f.base.hom.toRingHom).obj
      (ModuleCat.of X.base.carrier X.module) ⟶
      ModuleCat.of Y.base.carrier Y.module :=
  GroupRepCat.induced f.base f.toFun f.map_add f.map_smul

/-- A morphism is `f`-linear, `Γ`-equivariant, and induces an isomorphism after
extension of scalars. -/
theorem spec {X Y : GroupRepCat Γ Λ k} (f : Hom X Y) :
    (∀ (a : X.base.carrier) (m : X.module),
        f.toFun (a • m) = f.base.hom a • f.toFun m) ∧
      (∀ (γ : Γ) (m : X.module),
        f.toFun ((X.rho γ).val m) = (Y.rho γ).val (f.toFun m)) ∧
      IsIso f.induced := sorry

/-- The identity morphism has identity base arrow. -/
theorem id_base (X : GroupRepCat Γ Λ k) : (id X).base = 𝟙 X.base := sorry

/-- Composition of morphisms has composed base arrows. -/
theorem comp_base {X Y Z : GroupRepCat Γ Λ k} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).base = f.base ≫ g.base := sorry

end Hom

/-- The `End`-valued representation associated with the stored `GL`-action. -/
def toRepresentation (X : GroupRepCat Γ Λ k) :
    Representation X.base.carrier Γ X.module :=
  (Units.coeHom _).comp X.rho

/-- Reconstructing the `GL`-valued action from `toRepresentation` recovers `rho`. -/
theorem toRepresentation_asGroupHom (X : GroupRepCat Γ Λ k) :
    (toRepresentation X).asGroupHom = X.rho := sorry

/-- Category of finite projective representations of `Γ` over objects of
`ArtinianLocalAlgCat Λ k`. -/
instance category : Category.{u} (GroupRepCat Γ Λ k) where
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
def forget : GroupRepCat Γ Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj X := X.base
  map f := f.base
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor evaluates to the stored base algebra. -/
theorem forget_obj (X : GroupRepCat Γ Λ k) : (forget Γ Λ k).obj X = X.base := sorry

/-- The forgetful functor sends a morphism to its base arrow. -/
theorem forget_map {X Y : GroupRepCat Γ Λ k} (f : X ⟶ Y) :
    (forget Γ Λ k).map f = f.base := sorry

/-- The projection `p : GroupRepCat ⥤ ArtinianLocalAlgCat` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_forget :
    IsFibered.InGroupoids (forget Γ Λ k).op := sorry

/-- The residue object `x0 = (k, V, ρ0)` of a finite-dimensional `k`-representation. -/
def ofResidue {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) : GroupRepCat Γ Λ k where
  base := ArtinianLocalAlgCat.residue Λ k
  module := V
  finiteProjective := sorry
  rho := ρ0

/-- The base of `ofResidue ρ0` is the residue object of `ArtinianLocalAlgCat`. -/
theorem ofResidue_base {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    (ofResidue Γ Λ k ρ0).base = ArtinianLocalAlgCat.residue Λ k := sorry

/-- `x0 = (k, V, ρ0)` as an object of the residue fibre of `forget`. -/
def residueObj {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    (forget Γ Λ k).Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk (rfl : (forget Γ Λ k).obj (ofResidue Γ Λ k ρ0) = ArtinianLocalAlgCat.residue Λ k)

end Forget

end GroupRepCat
