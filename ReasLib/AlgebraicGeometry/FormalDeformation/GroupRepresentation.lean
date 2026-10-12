/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.RingTheory.Finiteness.Projective

/-! Finite projective representations over Artinian local algebras. -/

@[expose] public section

open CategoryTheory
open Functor
open scoped ChangeOfRings

universe u

variable (Γ Λ k : Type u) [Group Γ] [CommRing Λ] [IsNoetherianRing Λ] [Field k]
  [Algebra Λ k] [Module.Finite Λ k]

/-- A finite projective module over an Artinian local algebra with a `Γ`-action. -/
def GroupRepCat :=
  Σ' base : ArtinianLocalAlgCat Λ k, Σ' module : Type u,
    Σ' addCommGroup : AddCommGroup module,
      Σ' isModule : @Module base.carrier module _ addCommGroup.toAddCommMonoid,
        Σ' _ :
          @Module.FiniteProjective base.carrier module _ addCommGroup.toAddCommMonoid isModule,
          Γ →* @LinearMap.GeneralLinearGroup base.carrier module _
            addCommGroup.toAddCommMonoid isModule

namespace GroupRepCat

variable {Γ Λ k}

/-- The underlying Artinian local algebra of a representation. -/
def base (X : GroupRepCat Γ Λ k) : ArtinianLocalAlgCat Λ k := X.1

/-- The underlying module carrier of a representation. -/
def module (X : GroupRepCat Γ Λ k) : Type u := X.2.1

/-- The stored additive group structure of the representation module. -/
instance addCommGroup (X : GroupRepCat Γ Λ k) : AddCommGroup X.module := X.2.2.1

/-- The stored module structure over the base algebra. -/
instance isModule (X : GroupRepCat Γ Λ k) : Module X.base.carrier X.module := X.2.2.2.1

/-- Finite projectivity of the representation module over its base algebra. -/
theorem finiteProjective (X : GroupRepCat Γ Λ k) :
    Module.FiniteProjective X.base.carrier X.module := X.2.2.2.2.1

/-- The action of the group by invertible linear maps. -/
def rho (X : GroupRepCat Γ Λ k) :
    Γ →* LinearMap.GeneralLinearGroup X.base.carrier X.module := X.2.2.2.2.2

/-- Bundle a base algebra, a finite projective module, and a `Γ`-action. -/
def of (A : ArtinianLocalAlgCat Λ k) (M : Type u)
    [addCommGroup : AddCommGroup M] [isModule : Module A.carrier M]
    (hM : Module.FiniteProjective A.carrier M)
    (ρ : Γ →* LinearMap.GeneralLinearGroup A.carrier M) : GroupRepCat Γ Λ k :=
  ⟨A, M, addCommGroup, isModule, hM, ρ⟩

/-- Finite generation of the underlying module. -/
instance instModuleFinite (X : GroupRepCat Γ Λ k) : Module.Finite X.base.carrier X.module :=
  Module.FiniteProjective.finite X.finiteProjective

/-- Projectivity of the underlying module. -/
instance instModuleProjective (X : GroupRepCat Γ Λ k) :
    Module.Projective X.base.carrier X.module :=
  Module.FiniteProjective.projective X.finiteProjective

noncomputable section

/-- The semilinear map underlying a morphism over `f`. -/
def linearAlongHom {X Y : GroupRepCat Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module),
      g (a • m) = ArtinianLocalAlgCat.Hom.toRingHom f a • g m) :
    X.module →ₗ[X.base.carrier]
      ((ModuleCat.restrictScalars (ArtinianLocalAlgCat.Hom.toRingHom f)).obj
        (ModuleCat.of Y.base.carrier Y.module)) where
  toFun := g
  map_add' := map_add
  map_smul' := map_smul

/-- The module-category morphism induced by a semilinear map over `f`. -/
def linearAlong {X Y : GroupRepCat Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module),
      g (a • m) = ArtinianLocalAlgCat.Hom.toRingHom f a • g m) :
    ModuleCat.of X.base.carrier X.module ⟶
      (ModuleCat.restrictScalars (ArtinianLocalAlgCat.Hom.toRingHom f)).obj
        (ModuleCat.of Y.base.carrier Y.module) :=
  ConcreteCategory.ofHom (linearAlongHom f g map_add map_smul)

/-- The scalar-extension morphism adjunct to a semilinear map over `f`. -/
def induced {X Y : GroupRepCat Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module),
      g (a • m) = ArtinianLocalAlgCat.Hom.toRingHom f a • g m) :
    (ModuleCat.extendScalars (ArtinianLocalAlgCat.Hom.toRingHom f)).obj
      (ModuleCat.of X.base.carrier X.module) ⟶ ModuleCat.of Y.base.carrier Y.module :=
  ((ModuleCat.extendRestrictScalarsAdj (ArtinianLocalAlgCat.Hom.toRingHom f)).homEquiv
      (ModuleCat.of X.base.carrier X.module) (ModuleCat.of Y.base.carrier Y.module)).symm
    (linearAlong f g map_add map_smul)

/-- A morphism consists of a base arrow and an equivariant scalar-compatible map. -/
def Hom (X Y : GroupRepCat Γ Λ k) :=
  Σ' base : X.base ⟶ Y.base, Σ' toFun : X.module → Y.module,
    Σ' map_add : ∀ m₁ m₂, toFun (m₁ + m₂) = toFun m₁ + toFun m₂,
      Σ' map_smul : ∀ (a : X.base.carrier) (m : X.module),
        toFun (a • m) = ArtinianLocalAlgCat.Hom.toRingHom base a • toFun m,
        (∀ (γ : Γ) (m : X.module),
          toFun ((X.rho γ).val m) = (Y.rho γ).val (toFun m)) ∧
          IsIso (induced base toFun map_add map_smul)

namespace Hom

/-- The base arrow of a morphism of representations. -/
def base {X Y : GroupRepCat Γ Λ k} (f : Hom X Y) : X.base ⟶ Y.base := f.1

/-- The underlying function of a morphism of representations. -/
def toFun {X Y : GroupRepCat Γ Λ k} (f : Hom X Y) : X.module → Y.module := f.2.1

/-- A morphism of representations preserves addition. -/
theorem map_add {X Y : GroupRepCat Γ Λ k} (f : Hom X Y) :
    ∀ m₁ m₂, f.toFun (m₁ + m₂) = f.toFun m₁ + f.toFun m₂ := f.2.2.1

/-- A morphism of representations is semilinear over its base arrow. -/
theorem map_smul {X Y : GroupRepCat Γ Λ k} (f : Hom X Y) :
    ∀ (a : X.base.carrier) (m : X.module),
      f.toFun (a • m) = ArtinianLocalAlgCat.Hom.toRingHom f.base a • f.toFun m := f.2.2.2.1

/-- A morphism of representations commutes with the group actions. -/
theorem equivariant {X Y : GroupRepCat Γ Λ k} (f : Hom X Y) :
    ∀ (γ : Γ) (m : X.module),
      f.toFun ((X.rho γ).val m) = (Y.rho γ).val (f.toFun m) := f.2.2.2.2.1

/-- A morphism of representations becomes an isomorphism after extending scalars. -/
theorem inducesIso {X Y : GroupRepCat Γ Λ k} (f : Hom X Y) :
    IsIso (GroupRepCat.induced f.base f.toFun f.map_add f.map_smul) := f.2.2.2.2.2

/-- Package the data of a morphism of representations. -/
def of {X Y : GroupRepCat Γ Λ k} (base : X.base ⟶ Y.base) (toFun : X.module → Y.module)
    (map_add : ∀ m₁ m₂, toFun (m₁ + m₂) = toFun m₁ + toFun m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module),
      toFun (a • m) = ArtinianLocalAlgCat.Hom.toRingHom base a • toFun m)
    (equivariant : ∀ (γ : Γ) (m : X.module),
      toFun ((X.rho γ).val m) = (Y.rho γ).val (toFun m))
    (inducesIso : IsIso (GroupRepCat.induced base toFun map_add map_smul)) : Hom X Y :=
  ⟨base, toFun, map_add, map_smul, equivariant, inducesIso⟩

/-- The identity function on a representation module preserves addition. -/
theorem id_map_add (X : GroupRepCat Γ Λ k) :
    ∀ m₁ m₂ : X.module, (fun m => m) (m₁ + m₂) = (fun m => m) m₁ + (fun m => m) m₂ := sorry

/-- The identity function is semilinear over the identity base arrow. -/
theorem id_map_smul (X : GroupRepCat Γ Λ k) :
    ∀ (a : X.base.carrier) (m : X.module),
      (fun m => m) (a • m) = ArtinianLocalAlgCat.Hom.toRingHom (𝟙 X.base) a • (fun m => m) m := sorry

/-- The identity function commutes with the representation action. -/
theorem id_equivariant (X : GroupRepCat Γ Λ k) :
    ∀ γ m, (fun m => m) ((X.rho γ).val m) = (X.rho γ).val ((fun m => m) m) := sorry

/-- Scalar extension along the identity carries the identity function to an isomorphism. -/
theorem id_inducesIso (X : GroupRepCat Γ Λ k) :
    IsIso (GroupRepCat.induced (𝟙 X.base) (fun m => m) (id_map_add X) (id_map_smul X)) := sorry

/-- The identity morphism of a representation. -/
def id (X : GroupRepCat Γ Λ k) : Hom X X :=
  of (𝟙 X.base) (fun m => m) (id_map_add X) (id_map_smul X)
    (id_equivariant X) (id_inducesIso X)

/-- The composite function of two representation morphisms preserves addition. -/
theorem comp_map_add {X Y Z : GroupRepCat Γ Λ k} (f : Hom X Y) (g : Hom Y Z) :
    ∀ m₁ m₂, (g.toFun ∘ f.toFun) (m₁ + m₂) =
      (g.toFun ∘ f.toFun) m₁ + (g.toFun ∘ f.toFun) m₂ := sorry

/-- The composite function is semilinear over the composite base arrow. -/
theorem comp_map_smul {X Y Z : GroupRepCat Γ Λ k} (f : Hom X Y) (g : Hom Y Z) :
    ∀ (a : X.base.carrier) (m : X.module),
      (g.toFun ∘ f.toFun) (a • m) =
        ArtinianLocalAlgCat.Hom.toRingHom (f.base ≫ g.base) a • (g.toFun ∘ f.toFun) m := sorry

/-- Composition of the underlying functions preserves equivariance. -/
theorem comp_equivariant {X Y Z : GroupRepCat Γ Λ k} (f : Hom X Y) (g : Hom Y Z) :
    ∀ γ m, (g.toFun ∘ f.toFun) ((X.rho γ).val m) =
      (Z.rho γ).val ((g.toFun ∘ f.toFun) m) := sorry

/-- Composition of the underlying functions preserves scalar-extension invertibility. -/
theorem comp_inducesIso {X Y Z : GroupRepCat Γ Λ k} (f : Hom X Y) (g : Hom Y Z) :
    IsIso (GroupRepCat.induced (f.base ≫ g.base) (g.toFun ∘ f.toFun)
      (comp_map_add f g) (comp_map_smul f g)) := sorry

/-- Composition of morphisms of representations. -/
def comp {X Y Z : GroupRepCat Γ Λ k} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  of (f.base ≫ g.base) (g.toFun ∘ f.toFun) (comp_map_add f g) (comp_map_smul f g)
    (comp_equivariant f g) (comp_inducesIso f g)

/-- The scalar-extension morphism attached to a categorical morphism. -/
def induced {X Y : GroupRepCat Γ Λ k} (f : Hom X Y) :
    (ModuleCat.extendScalars (ArtinianLocalAlgCat.Hom.toRingHom f.base)).obj
      (ModuleCat.of X.base.carrier X.module) ⟶ ModuleCat.of Y.base.carrier Y.module :=
  GroupRepCat.induced f.base f.toFun f.map_add f.map_smul

/-- Equality follows from equality of base arrows and underlying functions. -/
theorem ext {X Y : GroupRepCat Γ Λ k} {f g : Hom X Y} (hbase : f.base = g.base)
    (hfun : f.toFun = g.toFun) : f = g := sorry

/-- The defining properties of a representation morphism. -/
theorem spec {X Y : GroupRepCat Γ Λ k} (f : Hom X Y) :
    (∀ a m, f.toFun (a • m) = ArtinianLocalAlgCat.Hom.toRingHom f.base a • f.toFun m) ∧
      (∀ γ m, f.toFun ((X.rho γ).val m) = (Y.rho γ).val (f.toFun m)) ∧
      IsIso f.induced := sorry

/-- The base of an identity morphism. -/
theorem id_base (X : GroupRepCat Γ Λ k) : (id X).base = 𝟙 X.base := sorry

/-- The base of a composite is the composite base morphism. -/
theorem comp_base {X Y Z : GroupRepCat Γ Λ k} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).base = f.base ≫ g.base := sorry

/-- Composition with an identity on the left is the original morphism. -/
theorem id_comp {X Y : GroupRepCat Γ Λ k} (f : Hom X Y) : comp (id X) f = f := sorry

/-- Composition with an identity on the right is the original morphism. -/
theorem comp_id {X Y : GroupRepCat Γ Λ k} (f : Hom X Y) : comp f (id Y) = f := sorry

/-- Composition of representation morphisms is associative. -/
theorem assoc {W X Y Z : GroupRepCat Γ Λ k} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- The endomorphism-valued representation associated to `rho`. -/
def toRepresentation (X : GroupRepCat Γ Λ k) :
    Representation X.base.carrier Γ X.module :=
  (Units.coeHom _).comp X.rho

/-- The `GL`-valued action is recovered from the endomorphism representation. -/
theorem toRepresentation_asGroupHom (X : GroupRepCat Γ Λ k) :
    (toRepresentation X).asGroupHom = X.rho := sorry

/-- The category structure on finite projective representations. -/
instance category : Category.{u} (GroupRepCat Γ Λ k) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

section Forget

variable (Γ Λ k)

/-- The projection from representations to Artinian local algebras. -/
def forget : GroupRepCat Γ Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj X := X.base
  map f := f.base
  map_id := Hom.id_base
  map_comp := Hom.comp_base

/-- The object map of the projection. -/
theorem forget_obj (X : GroupRepCat Γ Λ k) : (forget Γ Λ k).obj X = X.base := rfl

/-- The morphism map of the projection. -/
theorem forget_map {X Y : GroupRepCat Γ Λ k} (f : X ⟶ Y) :
    (forget Γ Λ k).map f = f.base := rfl

/-- The projection is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_forget :
    IsFibered.InGroupoids (forget Γ Λ k).op := sorry

/-- The residue representation as an object of the representation category. -/
def ofResidue {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) : GroupRepCat Γ Λ k :=
  of (ArtinianLocalAlgCat.residue Λ k) V (isModule := (inferInstance : Module k V))
    ⟨(inferInstance : Module.Finite k V), (inferInstance : Module.Projective k V)⟩ ρ0

/-- The base of the residue representation. -/
theorem ofResidue_base {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
    (ofResidue Γ Λ k ρ0).base = ArtinianLocalAlgCat.residue Λ k := by
  simp [ofResidue, of, base]

/-- The residue representation as an object of the residue fibre. -/
def residueObj {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :
  (forget Γ Λ k).Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk (a := ofResidue Γ Λ k ρ0) (ofResidue_base Γ Λ k ρ0)

/-- The deformation category associated to a residue representation. -/
abbrev deformation {V : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ0 : Γ →* LinearMap.GeneralLinearGroup k V) :=
  Over (Fiber.fiberInclusion.obj (residueObj Γ Λ k ρ0))

/-- The tensor generator formula for the induced morphism. -/
theorem induced_tmul {X Y : GroupRepCat Γ Λ k} (f : X.base ⟶ Y.base)
    (g : X.module → Y.module)
    (map_add : ∀ m₁ m₂, g (m₁ + m₂) = g m₁ + g m₂)
    (map_smul : ∀ (a : X.base.carrier) (m : X.module),
      g (a • m) = ArtinianLocalAlgCat.Hom.toRingHom f a • g m)
    (a : Y.base.carrier) (m : X.module) :
    induced f g map_add map_smul
      (a ⊗ₜ[X.base.carrier, ArtinianLocalAlgCat.Hom.toRingHom f] m) = a • g m := sorry

end Forget

end

end GroupRepCat
