module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.Points
import StacksCheckRecall

/-!
# An infinite fibre of points of algebraic spaces
-/

@[expose] public section

universe u

/- Example 68.18.2: for a characteristic-zero field with an infinite-order automorphism,
the simultaneous point fibre over the origin orbit and the unique spectrum point consists
exactly of the integer points. Together with their injectivity, this identifies it with ℤ. -/
@[stacks 0AC4] #check (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.fibre_eq_range_integerPoint :
  ∀ (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (hσ : ¬ IsOfFinOrder σ),
    AlgebraicGeometry.AlgebraicSpace.Points.fibre
      (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.p K σ)
      (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.q K)
      (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.x K σ)
      (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.z K) =
      Set.range (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.integerPoint K))

#check (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.isPullback :
  ∀ (K : Type u) [Field K] [CharZero K] (σ : RingAut K) (hσ : ¬ IsOfFinOrder σ),
    CategoryTheory.IsPullback
      (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.q K)
      (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.p K σ)
      (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.g K σ hσ)
      (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.f K σ hσ))

#check (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.integerPoint_injective :
  ∀ (K : Type u) [Field K] [CharZero K],
    Function.Injective (AlgebraicGeometry.AlgebraicSpace.InfiniteOrderFibre.integerPoint K))
