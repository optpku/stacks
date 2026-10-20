module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Basic
public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.TrivialSum
public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.Rank
public import Mathlib.Tactic.CrossRefAttribute
import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Coordinates

/-!
# Ranks of differentials in trivial finite free sums

This leaf records the coordinate consequences of the representation-independent
`FiniteFreeComplex.IsTrivialSum` property.  Keeping them here lets consumers of
the decomposition avoid importing local-ring hypotheses or a chapter file.
-/

@[expose] public section

open LinearMap

universe u

namespace FiniteFreeComplex.IsTrivialSum

variable {R : Type u} [CommRing R] [Nontrivial R] {e : ℕ}
variable {C : _root_.FiniteFreeComplex R e}

/-- The exterior rank of a displayed differential is the alternating tail
of the ranks of the complex. -/
@[stacks 00MW "exterior rank in a trivial finite free sum"]
theorem exteriorRank_diffAt
    (hC : FiniteFreeComplex.IsTrivialSum C.toChainComplex) (i : Fin e) :
    (exteriorRank (C.diffAt i) : ℤ) = C.alternatingRank i := sorry

/-- Exterior ranks of adjacent differentials add to the rank of their common
term. -/
@[stacks 00MW "adjacent exterior ranks in a trivial finite free sum"]
theorem exteriorRank_diffAt_add
    (hC : FiniteFreeComplex.IsTrivialSum C.toChainComplex)
    (i : FiniteFreeComplex.AdjacentIndex e) :
    exteriorRank (C.diffAt i.lower) + exteriorRank (C.diffAt i.upper) =
      C.rank i.term := by
  exact_mod_cast
    calc
      (exteriorRank (C.diffAt i.lower) : ℤ) +
          exteriorRank (C.diffAt i.upper) =
          C.alternatingRank i.lower + C.alternatingRank i.upper := by
            rw [exteriorRank_diffAt hC, exteriorRank_diffAt hC]
      _ = (C.rank i.term : ℤ) :=
        FiniteFreeComplex.alternatingRank.lower_add_upper C i

/-- The maximal nonzero minors of each displayed differential generate the
unit ideal. -/
@[stacks 00MW "maximal minors in a trivial finite free sum"]
theorem rankMinorIdeal_diffAt
    (hC : FiniteFreeComplex.IsTrivialSum C.toChainComplex) (i : Fin e) :
    I(C.diffAt i) = ⊤ := sorry

end FiniteFreeComplex.IsTrivialSum
