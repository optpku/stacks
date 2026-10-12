/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Group.ULift
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.ZMod.Basic
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback

/-!
# ℤ_[ℓ]-sheaves on the small étale site

A `ℤ_[ℓ]`-sheaf, also called an `ℓ`-adic sheaf, is a sequential inverse system of
constructible small-étale abelian sheaves with adic transition maps. Lisse sheaves
are the locally constant ones, and morphisms are morphisms of inverse systems.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The annihilation, adicity and constructibility laws of an ℓ-adic inverse system. -/
class IsZEllSheafSystem (X : Scheme.{u}) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] [IsNoetherian X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
    (system : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) : Prop where
  /-- Stage `n`, indexed by `F_{n+1}`, is annihilated by `ℓ^{n+1}`. -/
  isKilled : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (system.family n) = 0
  /-- The successor transition kills multiplication by `ℓ^{n+1}` on the next stage. -/
  step_comp_nsmul :
    ∀ n, ((ℓ ^ (n + 1)) • 𝟙 (system.family (n + 1))) ≫ system.stepMap n = 0
  /-- The successor transition identifies the next stage modulo `ℓ^{n+1}` with the current stage. -/
  isAdic :
    ∀ n, IsIso (cokernel.desc ((ℓ ^ (n + 1)) • 𝟙 (system.family (n + 1)))
      (system.stepMap n) (step_comp_nsmul n))
  /-- Each stage is constructible as a sheaf of `ZMod (ℓ^{n+1})`-modules on `X` étale. -/
  isConstructible :
    ∀ n, IsConstructibleEtale
      (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y : Scheme.{u}} (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
        IsFiniteLocallyConstantAddCommGrp G) (system.family n)


/-- The full subcategory of inverse systems satisfying the ℓ-adic sheaf laws. -/
abbrev ZEllSheaf (X : Scheme.{u}) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] [IsNoetherian X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}] :=
  ObjectProperty.FullSubcategory
    (fun G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) ↦
      IsZEllSheafSystem X ℓ G)

namespace ZEllSheaf

section Canonical

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- The actual inverse system underlying an ℓ-adic sheaf. -/
abbrev system (F : ZEllSheaf X ℓ) := F.obj

/-- Objects of the full subcategory satisfy the four ℓ-adic laws. -/
instance isZEllSheafSystem (F : ZEllSheaf X ℓ) : IsZEllSheafSystem X ℓ F.system :=
  F.property

/-- Construct an ℓ-adic sheaf from its inverse system and the four source laws. -/
def ofSystem (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hKilled : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0)
    (hStep : ∀ n, ((ℓ ^ (n + 1)) • 𝟙 (G.family (n + 1))) ≫ G.stepMap n = 0)
    (hAdic : ∀ n, IsIso (cokernel.desc ((ℓ ^ (n + 1)) • 𝟙 (G.family (n + 1)))
      (G.stepMap n) (hStep n)))
    (hConstructible : ∀ n, IsConstructibleEtale
      (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
        X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y : Scheme.{u}} (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
        IsFiniteLocallyConstantAddCommGrp H) (G.family n)) : ZEllSheaf X ℓ :=
  ⟨G, ⟨hKilled, hStep, hAdic, hConstructible⟩⟩

/-- Each stage is killed by the corresponding power of ℓ. -/
theorem isKilled (F : ZEllSheaf X ℓ) (n : ℕ) :
    (ℓ ^ (n + 1)) • 𝟙 (F.system.family n) = 0 := F.property.isKilled n

/-- The successor map kills the next reduction relation. -/
theorem step_comp_nsmul (F : ZEllSheaf X ℓ) (n : ℕ) :
    ((ℓ ^ (n + 1)) • 𝟙 (F.system.family (n + 1))) ≫ F.system.stepMap n = 0 :=
  F.property.step_comp_nsmul n

/-- The canonical cokernel comparison is an isomorphism. -/
theorem isAdic (F : ZEllSheaf X ℓ) (n : ℕ) :
    IsIso (cokernel.desc ((ℓ ^ (n + 1)) • 𝟙 (F.system.family (n + 1)))
      (F.system.stepMap n) (F.step_comp_nsmul n)) := F.property.isAdic n

/-- The stages of an ℓ-adic sheaf are constructible. -/
theorem isConstructible (F : ZEllSheaf X ℓ) (n : ℕ) :
    IsConstructibleEtale
      (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
        X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y : Scheme.{u}} (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
        IsFiniteLocallyConstantAddCommGrp G) (F.system.family n) := F.property.isConstructible n

end Canonical


/-- Canonical reduction `ZMod (ℓ^i) ⟶ ZMod (ℓ^j)` after universe lift, for `j ≤ i`. -/
def zmodPowHom (ℓ : ℕ) {i j : ℕ} (hji : j ≤ i) :
    AddCommGrpCat.of (ULift.{u} (ZMod (ℓ ^ i))) ⟶
      AddCommGrpCat.of (ULift.{u} (ZMod (ℓ ^ j))) :=
  AddCommGrpCat.ofHom
    (AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((ZMod.castHom (pow_dvd_pow ℓ hji) (ZMod (ℓ ^ j))).toAddMonoidHom.comp
        AddEquiv.ulift.toAddMonoidHom))

/-- The constant sheaf of `ZMod (ℓ^{n+1})`-modules on the small étale site. -/
abbrev constantStage (X : Scheme.{u}) (ℓ n : ℕ)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1)))))

/-- The constant inverse system of sheaves with value `ZMod (ℓ^{n+1})` at stage `n`. -/
def constantSystem (X : Scheme.{u}) (ℓ : ℕ)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] :
    SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) where
  obj n := constantStage X ℓ n.unop
  map {i j} f :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
      (zmodPowHom ℓ (Nat.succ_le_succ (leOfHom f.unop)))
  map_id := sorry
  map_comp := sorry

/-- Reduction maps of constant `ZMod` values are `zmodPowHom` after applying the constant sheaf. -/
theorem constantSystem_map (X : Scheme.{u}) (ℓ : ℕ)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (constantSystem X ℓ).map f =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (zmodPowHom ℓ (Nat.succ_le_succ (leOfHom f.unop))) := sorry

/-- The constant `ℤ_[ℓ]`-sheaf, whose stage `n` is the constant sheaf on `ZMod (ℓ^{n+1})`. -/
def constant (X : Scheme.{u}) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] [IsNoetherian X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}] :
    ZEllSheaf X ℓ :=
  ofSystem (constantSystem X ℓ) (by sorry) (by sorry) (by sorry) (by sorry)

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- The `n`th stage of a `ℤ_[ℓ]`-sheaf, corresponding to the positive-indexed sheaf `F_{n+1}`. -/
abbrev stage (F : ZEllSheaf X ℓ) (n : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  F.system.family n

/-- The positive-indexed component `F_n` for `n ≥ 1`, as the stage `n - 1`. -/
abbrev component (F : ZEllSheaf X ℓ) (n : ℕ+) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  F.stage n.natPred

/-- The successor transition `F.stage (n + 1) ⟶ F.stage n`. -/
abbrev stepMap (F : ZEllSheaf X ℓ) (n : ℕ) : F.stage (n + 1) ⟶ F.stage n :=
  F.system.stepMap n

/-- The transition `F.stage j ⟶ F.stage i` for `i ≤ j`. -/
abbrev transitionMap (F : ZEllSheaf X ℓ) {i j : ℕ} (hij : i ≤ j) :
    F.stage j ⟶ F.stage i :=
  F.system.transitionMap hij

/-- The cokernel comparison `coker (ℓ^{n+1} • 𝟙 F.stage (n + 1)) ⟶ F.stage n`. -/
def adicCokernel (F : ZEllSheaf X ℓ) (n : ℕ) :
    cokernel ((ℓ ^ (n + 1)) • 𝟙 (F.stage (n + 1))) ⟶ F.stage n :=
  cokernel.desc ((ℓ ^ (n + 1)) • 𝟙 (F.stage (n + 1))) (F.stepMap n)
    (F.step_comp_nsmul n)

/-- Stage `n` of a `ℤ_[ℓ]`-sheaf is the underlying inverse-system object at index `n`. -/
theorem stage_eq (F : ZEllSheaf X ℓ) (n : ℕ) :
    F.stage n = F.system.family n := sorry

/-- The positive-indexed component `F_n` is stage `n - 1`. -/
theorem component_eq (F : ZEllSheaf X ℓ) (n : ℕ+) :
    F.component n = F.stage n.natPred := sorry

/-- Successor transitions are the underlying sequential `stepMap`. -/
theorem stepMap_eq (F : ZEllSheaf X ℓ) (n : ℕ) :
    F.stepMap n = F.system.stepMap n := sorry

/-- Transitions for `i ≤ j` are the underlying sequential `transitionMap`. -/
theorem transitionMap_eq (F : ZEllSheaf X ℓ) {i j : ℕ} (hij : i ≤ j) :
    F.transitionMap hij = F.system.transitionMap hij := sorry

/-- The named adic comparison is the cokernel descent of `ℓ^{n+1} • 𝟙` along `stepMap`. -/
theorem adicCokernel_eq (F : ZEllSheaf X ℓ) (n : ℕ) :
    F.adicCokernel n =
      cokernel.desc ((ℓ ^ (n + 1)) • 𝟙 (F.stage (n + 1))) (F.stepMap n)
        (F.step_comp_nsmul n) := sorry

/-- The `n`th stage of the constant `ℤ_[ℓ]`-sheaf is the constant sheaf on `ZMod (ℓ^{n+1})`. -/
theorem constant_stage (n : ℕ) :
    (constant X ℓ).stage n = constantStage X ℓ n := sorry

/-- The positive-indexed component of the constant `ℤ_[ℓ]`-sheaf is the constant sheaf on `ZMod (ℓ^n)`. -/
theorem constant_component (n : ℕ+) :
    (constant X ℓ).component n =
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod (ℓ ^ (n : ℕ))))) := sorry

/-- Adicity is invertibility of the named cokernel comparison of each successor transition. -/
theorem isAdic_iff (F : ZEllSheaf X ℓ) (n : ℕ) :
    IsIso (F.adicCokernel n) ↔
      IsIso (cokernel.desc ((ℓ ^ (n + 1)) • 𝟙 (F.stage (n + 1))) (F.stepMap n)
        (F.step_comp_nsmul n)) := sorry

/-- Constructibility of a `ℤ_[ℓ]`-sheaf is stagewise constructibility of the underlying étale
sheaves. -/
theorem isConstructible_iff (F : ZEllSheaf X ℓ) :
    (∀ n, IsConstructibleEtale
      (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y : Scheme.{u}} (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
        IsFiniteLocallyConstantAddCommGrp G) (F.stage n)) ↔
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y : Scheme.{u}} (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp G) (F.system.family n) := sorry

/-- A `ℤ_[ℓ]`-sheaf is an adic inverse system of constructible stages killed by `ℓ^{n+1}`. -/
theorem spec (F : ZEllSheaf X ℓ) :
    (∀ n, (ℓ ^ (n + 1)) • 𝟙 (F.stage n) = 0) ∧
      (∀ n, ((ℓ ^ (n + 1)) • 𝟙 (F.stage (n + 1))) ≫ F.stepMap n = 0) ∧
      (∀ n, IsIso (F.adicCokernel n)) ∧
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y : Scheme.{u}} (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp G) (F.stage n) := sorry

/-- A `ℤ_[ℓ]`-sheaf is lisse when every stage is locally constant. -/
def IsLisse (F : ZEllSheaf X ℓ) : Prop :=
  ∀ n, Sheaf.IsLocallyConstant (F.stage n)

/-- Lisseness is stagewise local constancy of the underlying étale sheaves. -/
theorem isLisse_iff (F : ZEllSheaf X ℓ) :
    F.IsLisse ↔ ∀ n, Sheaf.IsLocallyConstant (F.stage n) := sorry

/-- The constant `ℤ_[ℓ]`-sheaf is lisse. -/
theorem constant_isLisse : (constant X ℓ).IsLisse := sorry

/-- A morphism of `ℤ_[ℓ]`-sheaves is a morphism of the underlying inverse systems. -/
abbrev Hom (F G : ZEllSheaf X ℓ) := F ⟶ G

/-- Forget an ℓ-adic sheaf morphism to its actual natural transformation. -/
abbrev hom {F G : ZEllSheaf X ℓ} (α : Hom F G) : F.system ⟶ G.system :=
  InducedCategory.Hom.hom α

/-- Lift a natural transformation between the underlying systems. -/
def homMk {F G : ZEllSheaf X ℓ} (α : F.system ⟶ G.system) : Hom F G :=
  ObjectProperty.homMk α

/-- The Hom correspondence with underlying inverse systems. -/
def homEquiv (F G : ZEllSheaf X ℓ) : Hom F G ≃ (F.system ⟶ G.system) :=
  InducedCategory.homEquiv

/-- The lifted morphism has the specified underlying natural transformation. -/
theorem hom_homMk {F G : ZEllSheaf X ℓ} (α : F.system ⟶ G.system) :
    hom (homMk α : Hom F G) = α := rfl

/-- Every morphism is recovered by lifting its underlying transformation. -/
theorem homMk_hom {F G : ZEllSheaf X ℓ} (α : Hom F G) :
    homMk (hom α) = α := by cases α; rfl

/-- The stage-`n` component of a morphism of `ℤ_[ℓ]`-sheaves. -/
def hom_app {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) : F.stage n ⟶ G.stage n :=
  (hom α).app (op n)

/-- Stage components of a morphism are the underlying natural transformation components. -/
theorem hom_app_eq {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    hom_app α n = (hom α).app (op n) := sorry

/-- A morphism of `ℤ_[ℓ]`-sheaves is a family of stage maps commuting with transitions. -/
theorem hom_iff {F G : ZEllSheaf X ℓ} (α : Hom F G) :
    (∀ n, hom_app α (n + 1) ≫ G.stepMap n = F.stepMap n ≫ hom_app α n) ∧
      (∀ {i j : ℕ} (hij : i ≤ j),
        hom_app α j ≫ G.transitionMap hij = F.transitionMap hij ≫ hom_app α i) := sorry

/-- The identity morphism of a `ℤ_[ℓ]`-sheaf. -/
def Hom.id (F : ZEllSheaf X ℓ) : Hom F F := 𝟙 F

/-- Composition of morphisms of `ℤ_[ℓ]`-sheaves. -/
def Hom.comp {F G H : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom G H) : Hom F H :=
  α ≫ β

/-- Identity morphisms act as identity maps on each stage. -/
theorem Hom.id_app (F : ZEllSheaf X ℓ) (n : ℕ) :
    hom_app (Hom.id F) n = 𝟙 (F.stage n) := sorry

/-- Composition of morphisms of `ℤ_[ℓ]`-sheaves is stagewise composition. -/
theorem Hom.comp_app {F G H : ZEllSheaf X ℓ} (α : Hom F G) (β : Hom G H) (n : ℕ) :
    hom_app (Hom.comp α β) n = hom_app α n ≫ hom_app β n := sorry

end ZEllSheaf

end AlgebraicGeometry.Scheme.Etale
