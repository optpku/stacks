/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.Topology.LocallyFinite.Refinement

/-!
# Rational equivalence of locally finite sums

This file gives a criterion for subordinate families of rational equivalences to combine into a
rational equivalence of locally finite sums.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RationalEquivalence

/-- Explicit boundary presentations carried by a locally finite family of closed subsets combine
into a rational equivalence between the corresponding locally finite sums of cycles. -/
theorem locallyFiniteSum_of_supported
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) [IsDimensionFunction d] (k : ℤ)
    {I : Type u} {J : I → Type u} (T : I → Closeds X)
    (α β : I → CycleGroup X d k)
    (hT : LocallyFinite fun i ↦ (T i : Set X))
    (hαT : ∀ i, (CycleGroup.toAlgebraicCycle d k (α i)).support ⊆ (T i : Set X))
    (hβT : ∀ i, (CycleGroup.toAlgebraicCycle d k (β i)).support ⊆ (T i : Set X))
    (x : (i : I) → J i → X)
    (hx : ∀ i j, d (x i j) = k + 1)
    (r : ∀ i j, (Scheme.PointClosure.scheme (x i j)).functionFieldˣ)
    (hlocal : ∀ i, LocallyFinite fun j ↦
      (Scheme.PointClosure.closedSubset (x i j) : Set X))
    (hcontained : ∀ i j, Scheme.PointClosure.closedSubset (x i j) ≤ T i)
    (hboundary : ∀ i, α i - β i =
      RationalEquivalence.boundary d k (x i) (hx i) (r i) (hlocal i)) :
    RationallyEquivalent d k
      (CycleGroup.locallyFiniteSum d k α (hT.subset hαT))
      (CycleGroup.locallyFiniteSum d k β (hT.subset hβT)) := sorry

/-- For cycles graded by a relative dimension function, explicit boundary presentations carried by
a locally finite family of closed subsets combine into a rational equivalence of locally finite
sums. -/
theorem relativeLocallyFiniteSum_of_supported
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
    {I : Type u} {J : I → Type u} (T : I → Closeds X)
    (α β : I → CycleGroup X (f.relativeDimensionFunction δ) k)
    (hT : LocallyFinite fun i ↦ (T i : Set X))
    (hαT : ∀ i, (CycleGroup.toAlgebraicCycle (f.relativeDimensionFunction δ) k
      (α i)).support ⊆ (T i : Set X))
    (hβT : ∀ i, (CycleGroup.toAlgebraicCycle (f.relativeDimensionFunction δ) k
      (β i)).support ⊆ (T i : Set X))
    (x : (i : I) → J i → X)
    (hx : ∀ i j, f.relativeDimensionFunction δ (x i j) = k + 1)
    (r : ∀ i j, (Scheme.PointClosure.scheme (x i j)).functionFieldˣ)
    (hlocal : ∀ i, LocallyFinite fun j ↦
      (Scheme.PointClosure.closedSubset (x i j) : Set X))
    (hcontained : ∀ i j, Scheme.PointClosure.closedSubset (x i j) ≤ T i)
    (hboundary : ∀ i, α i - β i =
      @RationalEquivalence.boundary X (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) inferInstance k (J i)
        (x i) (hx i) (r i) (hlocal i)) :
    @RationalEquivalence.RationallyEquivalent X
      (LocallyOfFiniteType.isLocallyNoetherian f) (f.relativeDimensionFunction δ)
      inferInstance k
      (CycleGroup.locallyFiniteSum (f.relativeDimensionFunction δ) k α (hT.subset hαT))
      (CycleGroup.locallyFiniteSum (f.relativeDimensionFunction δ) k β (hT.subset hβT)) := sorry

end AlgebraicGeometry.RationalEquivalence
