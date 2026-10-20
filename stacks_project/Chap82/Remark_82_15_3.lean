module

public import ReasLib.Topology.LocallyFinite.Refinement
public import stacks_project.Chap82.Definition_82_15_1_RationalEquivalence
public import stacks_project.Chap82.Remark_82_15_3_Sum

/-!
# Rational equivalence of locally finite sums of algebraic-space cycles

When pairwise rational equivalences of `k`-cycles are given by presentations
supported on a locally finite family of closed subsets, the locally finite sums
are rationally equivalent.
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

/-- Remark 82.15.3: In Situation 82.2.1, for good `X / B` and locally finite
families of `k`-cycles `α i`, `β i` whose pairwise rational equivalences are
given by presentations `W i j`, `φ i j` supported on a locally finite family of
closed sets `T i`, the locally finite sums are rationally equivalent. Pairwise
rational equivalence alone need not pass to the sums, because the witnessing
integral closed subspaces may fail to be jointly locally finite; when each
`|W i j|` lies in `T i`, the sigma-indexed family is automatically locally
finite and the difference of the sums is the corresponding boundary. -/
@[stacks 0EQ8]
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

/-- The difference of the locally finite sums is the official boundary of the
sigma-indexed family of integral closed subspaces contained in the `T i`. -/
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

end Hom

end AlgebraicGeometry.AlgebraicSpace
