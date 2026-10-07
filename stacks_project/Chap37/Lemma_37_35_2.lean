module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.FiniteSeparable
import StacksCheckRecall

universe u v

/- Lemma 37.35.2: every finite separable extension of the residue field at a point of a
scheme is realized as the residue field at the selected point of an étale neighbourhood. -/
@[stacks 02LF] #check
  (AlgebraicGeometry.Scheme.EtaleNeighborhood.exists_residueFieldEquiv :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (s : S)
      (k : Type v) [Field k] [Algebra (S.residueField s) k]
      [FiniteDimensional (S.residueField s) k]
      [Algebra.IsSeparable (S.residueField s) k],
      ∃ U : AlgebraicGeometry.Scheme.EtaleNeighborhood S s,
        Nonempty (U.toEtale.left.residueField U.point ≃ₐ[S.residueField s] k))
