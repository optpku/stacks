module

public import ReasLib.CategoryTheory.InverseSystem.Sequential.ModNsmul
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf

/-!
# Eventual values of reduced ℓ-adic systems

The stages are limits of the actual quotient systems. Their transition maps are
induced by the canonical quotient reductions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section
universe u

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
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) :
    ZEllSheaf X ℓ :=
  ofSystem (eventualSystem G ℓ) (by sorry) (by sorry) (by sorry) (by sorry)

/-- Stages of `ofEventuallyConstant` are the stages of `eventualSystem`. -/
theorem ofEventuallyConstant_stage
    (G : SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (h_killed : ∀ n, (ℓ ^ (n + 1)) • 𝟙 (G.family n) = 0)
    (h_constructible :
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
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
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
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
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
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
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F) (G.family n))
    (h_eventuallyConstant : G.IsEventuallyConstantModNsmul ℓ) :
    (∀ n, (ℓ ^ (n + 1)) • 𝟙
        ((ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).stage n) = 0) ∧
      (∀ n, IsIso
        ((ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).adicCokernel n)) ∧
      ∀ n, IsConstructibleEtale
        (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦ ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y : Scheme.{u}} (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
          IsFiniteLocallyConstantAddCommGrp F)
        ((ofEventuallyConstant G h_killed h_constructible h_eventuallyConstant).stage n) := sorry

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
