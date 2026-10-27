/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.LocallyFiniteSum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.LocallyFiniteSum
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open Function Set Topology TopologicalSpace

universe u v

/- Remark 82.15.3: In Situation 82.2.1, boundary presentations supported on
locally finite closed sets give rational equivalence of the locally finite
sums. Individual rational equivalences do not by themselves supply a jointly
locally finite presentation, so passing to sums requires this additional
justification; no counterexample is asserted. -/
@[stacks 0EQ8] #check (AlgebraicGeometry.AlgebraicSpace.Hom.rationallyEquivalent_locallyFiniteSum_of_supported :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (k : ℤ) {I : Type u} {J : I → Type u} (T : I → Closeds (Points X))
    (α β : I → AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f δ k)
    (hT : LocallyFinite fun i ↦ (T i).carrier)
    (hαT : ∀ i, (α i : Function.locallyFinsupp (Points X) ℤ).support ⊆ (T i).carrier)
    (hβT : ∀ i, (β i : Function.locallyFinsupp (Points X) ℤ).support ⊆ (T i).carrier)
    (W : (i : I) → J i → ClosedSubspace X)
    (hW_int : ∀ i j, IsIntegral (W i j).X)
    (hW_dim : ∀ i j, AlgebraicGeometry.AlgebraicSpace.Hom.deltaDimension f δ
      (@ClosedSubspace.irreducibleClosed S X (W i j) (hW_int i j)) = k + 1)
    (φ : ∀ i j, (RationalFunction (W i j).X)ˣ)
    (hlocal : ∀ i, LocallyFinite fun j ↦ (W i j).pointsSet)
    (hcontained : ∀ i j, (W i j).pointsSet ⊆ (T i).carrier)
    (hboundary : ∀ i, α i - β i =
      RationalEquivalence.boundary f δ k (W i) (hW_int i) (hW_dim i) (φ i)
        (hlocal i)),
    RationalEquivalence.RationallyEquivalent f δ k
      (locallyFiniteSum f δ k α (hT.subset hαT))
      (locallyFiniteSum f δ k β (hT.subset hβT)))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.locallyFiniteSum_sub_eq_boundary_of_supported :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (k : ℤ) {I : Type u} {J : I → Type u} (T : I → Closeds (Points X))
    (α β : I → AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f δ k)
    (hT : LocallyFinite fun i ↦ (T i).carrier)
    (hαT : ∀ i, (α i : Function.locallyFinsupp (Points X) ℤ).support ⊆ (T i).carrier)
    (hβT : ∀ i, (β i : Function.locallyFinsupp (Points X) ℤ).support ⊆ (T i).carrier)
    (W : (i : I) → J i → ClosedSubspace X)
    (hW_int : ∀ i j, IsIntegral (W i j).X)
    (hW_dim : ∀ i j, AlgebraicGeometry.AlgebraicSpace.Hom.deltaDimension f δ
      (@ClosedSubspace.irreducibleClosed S X (W i j) (hW_int i j)) = k + 1)
    (φ : ∀ i j, (RationalFunction (W i j).X)ˣ)
    (hlocal : ∀ i, LocallyFinite fun j ↦ (W i j).pointsSet)
    (hcontained : ∀ i j, (W i j).pointsSet ⊆ (T i).carrier)
    (hboundary : ∀ i, α i - β i =
      RationalEquivalence.boundary f δ k (W i) (hW_int i) (hW_dim i) (φ i)
        (hlocal i)),
    locallyFiniteSum f δ k α (hT.subset hαT) -
      locallyFiniteSum f δ k β (hT.subset hβT) =
      RationalEquivalence.boundary f δ k (fun p : Σ i, J i ↦ W p.1 p.2)
        (fun p ↦ hW_int p.1 p.2) (fun p ↦ hW_dim p.1 p.2)
        (fun p ↦ φ p.1 p.2)
        (LocallyFinite.sigma_of_subset hT hlocal hcontained))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.locallyFiniteSum_mem :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ) (k : ℤ)
    {I : Type v} (α : I → (cycleGroup f δ k))
    (hα : LocallyFinite fun i ↦
      (α i : Function.locallyFinsupp (Points X) ℤ).support),
    AlgebraicCycle.locallyFiniteSum
      (fun i ↦ (α i : Function.locallyFinsupp (Points X) ℤ)) hα ∈
        (cycleGroup f δ k))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.locallyFiniteSum :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ) (k : ℤ)
    {I : Type v} (α : I → (cycleGroup f δ k))
    (hα : LocallyFinite fun i ↦
      (α i : Function.locallyFinsupp (Points X) ℤ).support),
    (cycleGroup f δ k))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.locallyFiniteSum_apply :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFiniteType f] (δ : Points B → ℤ) (k : ℤ)
    {I : Type v} (α : I → (cycleGroup f δ k))
    (hα : LocallyFinite fun i ↦
      (α i : Function.locallyFinsupp (Points X) ℤ).support)
    (x : Points X),
    (locallyFiniteSum f δ k α hα : Function.locallyFinsupp (Points X) ℤ) x =
      ∑ᶠ i, (α i : Function.locallyFinsupp (Points X) ℤ) x)

#check (AlgebraicGeometry.AlgebraicCycle.geometricSupport :
  ∀ {Y : Type u} [TopologicalSpace Y] {R : Type v} [Zero R],
    Function.locallyFinsupp Y R → Set Y)

#check (AlgebraicGeometry.AlgebraicCycle.geometricSupport_def :
  ∀ {Y : Type u} [TopologicalSpace Y] {R : Type v} [Zero R]
    (α : Function.locallyFinsupp Y R),
    AlgebraicCycle.geometricSupport α = ⋃ x ∈ Function.support α, closure {x})

#check (AlgebraicGeometry.AlgebraicCycle.mem_geometricSupport :
  ∀ {Y : Type u} [TopologicalSpace Y] {R : Type v} [Zero R]
    (α : Function.locallyFinsupp Y R) (y : Y),
    y ∈ AlgebraicCycle.geometricSupport α ↔ ∃ x : Y, α x ≠ 0 ∧ y ∈ closure {x})

#check (AlgebraicGeometry.AlgebraicCycle.isClosed_geometricSupport :
  ∀ {Y : Type u} [TopologicalSpace Y] {R : Type v} [Zero R]
    (α : Function.locallyFinsupp Y R),
    IsClosed (AlgebraicCycle.geometricSupport α))

#check (AlgebraicGeometry.AlgebraicCycle.geometricSupport_subset_closed_iff :
  ∀ {Y : Type u} [TopologicalSpace Y] {R : Type v} [Zero R]
    (α : Function.locallyFinsupp Y R) (T : Closeds Y),
    AlgebraicCycle.geometricSupport α ⊆ T.carrier ↔ α.support ⊆ T.carrier)
