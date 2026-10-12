/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.LocallyFiniteSum

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

/- Remark 42.19.6: rational equivalences between families of `k`-cycles carried by a locally
finite family of closed subsets combine into a rational equivalence between their locally finite
sums. -/
@[stacks 02RZ] #check
  (AlgebraicGeometry.RationalEquivalence.relativeLocallyFiniteSum_of_supported :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
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
          (x i) (hx i) (r i) (hlocal i)),
      @RationalEquivalence.RationallyEquivalent X
        (LocallyOfFiniteType.isLocallyNoetherian f) (f.relativeDimensionFunction δ)
        inferInstance k
        (CycleGroup.locallyFiniteSum (f.relativeDimensionFunction δ) k α (hT.subset hαT))
        (CycleGroup.locallyFiniteSum (f.relativeDimensionFunction δ) k β (hT.subset hβT)))
