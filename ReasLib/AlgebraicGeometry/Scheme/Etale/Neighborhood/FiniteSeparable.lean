/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.ResidueField
public import ReasLib.RingTheory.Etale.Point.FiniteSeparable

@[expose] public section

universe u v

namespace AlgebraicGeometry.Scheme.EtaleNeighborhood

/-- Every finite separable extension of the residue field at a point of a
scheme is realized by the residue field at the selected point of an étale
neighbourhood. -/
@[stacks 02LF]
theorem exists_residueFieldEquiv (S : Scheme.{u}) (s : S)
    (k : Type v) [Field k] [Algebra (S.residueField s) k]
    [FiniteDimensional (S.residueField s) k]
    [Algebra.IsSeparable (S.residueField s) k] :
    ∃ U : EtaleNeighborhood S s,
      Nonempty (U.toEtale.left.residueField U.point ≃ₐ[S.residueField s] k) := sorry

end AlgebraicGeometry.Scheme.EtaleNeighborhood
