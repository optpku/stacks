module

public import ReasLib.RingTheory.MvPolynomial.GraphSurface
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.60.3: over an algebraically closed field `k`, the classical closed subset
of `k⁵` defined by `x 0 ^ 2 = x 3`, `x 1 ^ 5 = x 4`, and
`x 2 ^ 2 + x 2 + x 3 + x 4 = 0` has dimension `2`.
The classical Zariski topology is induced by evaluation into the prime spectrum.
The dimension comparison equates its topological Krull dimension with the ring
Krull dimension of its quotient coordinate ring.
`mem_classicalZeroLocus_iff` identifies the classical locus with these equations.
Eliminating the last two coordinates leaves the hypersurface
`X 2 ^ 2 + X 2 + X 0 ^ 2 + X 1 ^ 5 = 0` in three variables. -/
@[stacks 0EEM] #check
  (MvPolynomial.GraphSurface.topologicalKrullDim_zeroLocus :
    ∀ (k : Type u) [Field k] [IsAlgClosed k],
      topologicalKrullDim (MvPolynomial.ClassicalZeroLocus
        (MvPolynomial.GraphSurface.ideal k)) = 2)

#check (MvPolynomial.GraphSurface.mem_classicalZeroLocus_iff :
  ∀ {k : Type u} [Field k] (x : Fin 5 → k),
    x ∈ MvPolynomial.zeroLocus k (MvPolynomial.GraphSurface.ideal k) ↔
      x 0 ^ 2 = x 3 ∧ x 1 ^ 5 = x 4 ∧ x 2 ^ 2 + x 2 + x 3 + x 4 = 0)

#check (MvPolynomial.GraphSurface.ringKrullDim_coordinateRing :
  ∀ (k : Type u) [Field k], ringKrullDim (MvPolynomial.GraphSurface.CoordinateRing k) = 2)
