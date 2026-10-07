module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.InverseSystem.Sequential.EventuallyConstant
public import stacks_project.Chap64.Definition_64_18_1_ZEllSheaf

/-!
# Eventually constant nsmul reductions of sequential inverse systems

This leaf constructs the reduced inverse system `G / ℓ^{k+1} G` of nsmul cokernels, the
canonical `k+1 → k` reduction maps, the inverse-limit eventual system `{F_k}`, and the
constructor packaging that system as a `ℤ_[ℓ]`-sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u v

namespace CategoryTheory.Limits

/-- The cokernel of multiplication by `n` on an object of a preadditive category. -/
abbrev nsmulCokernel {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
    (X : C) (n : ℕ) : C :=
  cokernel (n • 𝟙 X)

/-- `nsmulCokernel` is the cokernel of `n • 𝟙`. -/
theorem nsmulCokernel_eq {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
    (X : C) (n : ℕ) :
    nsmulCokernel X n = cokernel (n • 𝟙 X) := sorry

/-- The map of nsmul cokernels induced by a morphism of objects. -/
def nsmulCokernelMap {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
    {X Y : C} (n : ℕ) (f : X ⟶ Y) :
    nsmulCokernel X n ⟶ nsmulCokernel Y n :=
  cokernel.map (n • 𝟙 X) (n • 𝟙 Y) f f
    ((nsmul_comp (𝟙 X) f n).trans
      ((congrArg (fun h => n • h) ((Category.id_comp f).trans (Category.comp_id f).symm)).trans
        (comp_nsmul f (𝟙 Y) n).symm))

/-- `nsmulCokernelMap` intertwines the cokernel projections. -/
theorem nsmulCokernelMap_π {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
    {X Y : C} (n : ℕ) (f : X ⟶ Y) :
    cokernel.π (n • 𝟙 X) ≫ nsmulCokernelMap n f = f ≫ cokernel.π (n • 𝟙 Y) := sorry

/-- The canonical reduction `coker ((b * m) • 𝟙 X) ⟶ coker (b • 𝟙 X)` along `m • 𝟙 X`. -/
def nsmulCokernelReduce {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
    (X : C) (m b : ℕ) :
    nsmulCokernel X (b * m) ⟶ nsmulCokernel X b :=
  cokernel.map ((b * m) • 𝟙 X) (b • 𝟙 X) (m • 𝟙 X) (𝟙 X)
    ((Category.comp_id ((b * m) • 𝟙 X)).trans
      ((mul_nsmul (𝟙 X) b m).trans
        ((congrArg (fun h => m • h) (Category.id_comp (b • 𝟙 X)).symm).trans
          (nsmul_comp (𝟙 X) (b • 𝟙 X) m).symm)))

/-- `nsmulCokernelReduce` identifies the two cokernel projections. -/
theorem nsmulCokernelReduce_π {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
    (X : C) (m b : ℕ) :
    cokernel.π ((b * m) • 𝟙 X) ≫ nsmulCokernelReduce X m b =
      cokernel.π (b • 𝟙 X) := sorry

end CategoryTheory.Limits

namespace CategoryTheory.SequentialInverseSystem

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]

/-- The object `G_n / ℓ^{k+1} G_n` at a 0-based stage. -/
def modNsmulFamily (G : SequentialInverseSystem C) (ℓ k n : ℕ) : C :=
  nsmulCokernel (G.family n) (ℓ ^ (k + 1))

/-- The successor map `G_{n+1} / ℓ^{k+1} G_{n+1} ⟶ G_n / ℓ^{k+1} G_n`. -/
def modNsmulStepMap (G : SequentialInverseSystem C) (ℓ k n : ℕ) :
    modNsmulFamily G ℓ k (n + 1) ⟶ modNsmulFamily G ℓ k n :=
  nsmulCokernelMap (ℓ ^ (k + 1)) (G.stepMap n)

/-- The inverse system of nsmul cokernels `G_n / ℓ^{k+1} G_n`. -/
def modNsmulSystem (G : SequentialInverseSystem C) (ℓ k : ℕ) :
    SequentialInverseSystem C :=
  Functor.ofOpSequence (modNsmulStepMap G ℓ k)

/-- Stage `n` of the reduced system is the nsmul cokernel of the original stage. -/
theorem modNsmulSystem_obj (G : SequentialInverseSystem C) (ℓ k n : ℕ) :
    (G.modNsmulSystem ℓ k).family n = modNsmulFamily G ℓ k n := sorry

/-- Successor maps of the reduced system are the named nsmul cokernel maps. -/
theorem modNsmulSystem_stepMap (G : SequentialInverseSystem C) (ℓ k n : ℕ) :
    (G.modNsmulSystem ℓ k).stepMap n = modNsmulStepMap G ℓ k n := sorry

/-- The source-indexed reduction `G_n / ℓ^k G_n`. -/
abbrev modNsmulComponent (G : SequentialInverseSystem C) (ℓ : ℕ) (k n : ℕ+) : C :=
  (G.modNsmulSystem ℓ k.natPred).family n.natPred

/-- The source component `G_n / ℓ^k G_n` is the nsmul cokernel at 0-based stages `n-1`. -/
theorem modNsmulComponent_eq (G : SequentialInverseSystem C) (ℓ : ℕ) (k n : ℕ+) :
    modNsmulComponent G ℓ k n = modNsmulFamily G ℓ k.natPred n.natPred := sorry

/-- The displayed successor `G_{n+1} / ℓ^k G_{n+1} ⟶ G_n / ℓ^k G_n`. -/
theorem modNsmulComponent_stepMap (G : SequentialInverseSystem C) (ℓ : ℕ) (k n : ℕ+) :
    (G.modNsmulSystem ℓ k.natPred).stepMap n.natPred =
      modNsmulStepMap G ℓ k.natPred n.natPred := sorry

/-- The pointwise reduction `G_n / ℓ^{k+2} G_n ⟶ G_n / ℓ^{k+1} G_n`. -/
def modNsmulReduceApp (G : SequentialInverseSystem C) (ℓ k n : ℕ) :
    modNsmulFamily G ℓ (k + 1) n ⟶ modNsmulFamily G ℓ k n :=
  nsmulCokernelReduce (G.family n) ℓ (ℓ ^ (k + 1))

/-- The reduction natural transformation `G / ℓ^{k+2} G ⟶ G / ℓ^{k+1} G`. -/
def modNsmulReduce (G : SequentialInverseSystem C) (ℓ k : ℕ) :
    G.modNsmulSystem ℓ (k + 1) ⟶ G.modNsmulSystem ℓ k :=
  NatTrans.ofOpSequence (modNsmulReduceApp G ℓ k) (fun _ ↦ sorry)

/-- Components of `modNsmulReduce` are the pointwise nsmul cokernel reductions. -/
theorem modNsmulReduce_app (G : SequentialInverseSystem C) (ℓ k n : ℕ) :
    (G.modNsmulReduce ℓ k).app (op n) = modNsmulReduceApp G ℓ k n := sorry

/-- Eventual constancy of every reduced system `G / ℓ^{k+1} G`. -/
def IsEventuallyConstantModNsmul (G : SequentialInverseSystem C) (ℓ : ℕ) : Prop :=
  ∀ k, ∃ N, (G.modNsmulSystem ℓ k).IsEventuallyConstantTo (op N)

/-- Eventual constancy of reductions is invertibility of late reduced successor maps. -/
theorem isEventuallyConstantModNsmul_iff (G : SequentialInverseSystem C) (ℓ : ℕ) :
    G.IsEventuallyConstantModNsmul ℓ ↔
      ∀ k, ∃ N, ∀ n, N ≤ n → IsIso ((G.modNsmulSystem ℓ k).stepMap n) := sorry

end CategoryTheory.SequentialInverseSystem

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

open CategoryTheory.SequentialInverseSystem
open CategoryTheory.Limits

variable {X : Scheme.{u}}
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- The inverse-limit value of the reduced tower `G / ℓ^{k+1} G`. -/
def eventualFamily
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (ℓ k : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  limit (G.modNsmulSystem ℓ k)

/-- The successor map of eventual values induced by reducing `ℓ^{k+2}` to `ℓ^{k+1}`. -/
def eventualStepMap
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (ℓ k : ℕ) :
    eventualFamily G ℓ (k + 1) ⟶ eventualFamily G ℓ k :=
  limMap (G.modNsmulReduce ℓ k)

/-- The inverse system whose stage `k` is the inverse limit of `G / ℓ^{k+1} G`. -/
def eventualSystem
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (ℓ : ℕ) :
    SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  Functor.ofOpSequence (eventualStepMap G ℓ)

/-- Stage `k` of the eventual system is the limit of the `ℓ^{k+1}`-reduced tower. -/
theorem eventualSystem_obj
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (ℓ k : ℕ) :
    (eventualSystem G ℓ).family k = limit (G.modNsmulSystem ℓ k) := sorry

variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]

/-- The `ℤ_[ℓ]`-sheaf whose stages are the eventual values of the reduced towers of `G`. -/
def ofEventuallyConstant
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_killed : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0)
    (h_constructible :
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ (etaleAbelianRestriction f).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) :
    ZEllSheaf X ℓ where
  system := eventualSystem G ℓ
  isKilled := sorry
  step_comp_nsmul := sorry
  isAdic := sorry
  isConstructible := sorry

/-- Stages of `ofEventuallyConstant` are the stages of `eventualSystem`. -/
theorem ofEventuallyConstant_stage
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_killed : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0)
    (h_constructible :
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ (etaleAbelianRestriction f).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) (k : ℕ) :
    (ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).stage k =
      (eventualSystem G ℓ).family k := sorry

/-- The source component `F_k` is stage `k-1` of `ofEventuallyConstant`. -/
theorem ofEventuallyConstant_component
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_killed : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0)
    (h_constructible :
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ (etaleAbelianRestriction f).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) (k : ℕ+) :
    (ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).component k =
      (eventualSystem G ℓ).family k.natPred := sorry

/-- Stage `k` of the constructed sheaf is an eventual value of `G / ℓ^{k+1} G`. -/
theorem ofEventuallyConstant_isEventuallyConstantWithValue
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_killed : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0)
    (h_constructible :
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ (etaleAbelianRestriction f).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) (k : ℕ) :
    (G.modNsmulSystem ℓ k).IsEventuallyConstantWithValue
      ((ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).stage k) := sorry

/-- Late projections from the reduced system to its inverse limit are isomorphisms. -/
theorem isIso_limit_π
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) (k : ℕ) :
    ∃ N, ∀ n, N ≤ n → IsIso (limit.π (G.modNsmulSystem ℓ k) (op n)) := sorry

/-- The constructed inverse system is killed by `ℓ^{n+1}`, adic, and constructible. -/
theorem ofEventuallyConstant_spec
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_killed : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0)
    (h_constructible :
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ (etaleAbelianRestriction f).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) :
    (∀ n, (ℓ ^ (n + 1)) • 𝟙
        ((ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).stage n) = 0) ∧
      (∀ n, IsIso
        ((ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).adicCokernel n)) ∧
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ (etaleAbelianRestriction f).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F)
        ((ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).stage n) := sorry

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
