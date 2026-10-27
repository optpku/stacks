/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.LocallyFiniteSum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RationalEquivalence
public import ReasLib.Topology.LocallyFinite.Refinement

/-!
# Rational equivalence of locally finite sums on algebraic spaces

Boundary presentations contained in a locally finite family of closed subsets
combine into a locally finite presentation for the difference of cycle sums.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]

/-- The difference of locally finite sums of cycles is the boundary of the
sigma-indexed family of integral closed subspaces presenting the individual
differences, when each presentation is contained in its member of a locally
finite family of closed sets. -/
theorem locallyFiniteSum_sub_eq_boundary_of_supported
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
        (hlocal i)) :
    locallyFiniteSum f δ k α (hT.subset hαT) -
      locallyFiniteSum f δ k β (hT.subset hβT) =
      RationalEquivalence.boundary f δ k (fun p : Σ i, J i ↦ W p.1 p.2)
        (fun p ↦ hW_int p.1 p.2) (fun p ↦ hW_dim p.1 p.2)
        (fun p ↦ φ p.1 p.2)
        (LocallyFinite.sigma_of_subset hT hlocal hcontained) :=
  sorry

/-- Locally finite sums of cycles are rationally equivalent when their
pairwise boundary presentations are supported on a locally finite family of
closed subsets.

Both presentation index types lie in the ambient universe of the base scheme.
Presentations in larger universes can be accommodated by reindexing them into
the size allowed by rational triviality; this extension requires a separate
size reindexing argument. -/
theorem rationallyEquivalent_locallyFiniteSum_of_supported
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
        (hlocal i)) :
    RationalEquivalence.RationallyEquivalent f δ k
      (locallyFiniteSum f δ k α (hT.subset hαT))
      (locallyFiniteSum f δ k β (hT.subset hβT)) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
