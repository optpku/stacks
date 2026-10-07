module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.FourByFour
import StacksCheckRecall

universe u

/- Example 42.68.23: for a field `k` and units `u₁`, `u₂`, `v₁`, and `v₂`, the
determinant of the exact two-periodic complex with the displayed sparse differentials is
the residue-field image of `-(u₁ * u₂) / (v₁ * v₂)`. -/
@[stacks 02PT] #check
  (CategoryTheory.TwoPeriodicEndomorphism.FourByFour.determinant_eq :
    ∀ {k : Type u} [Field k] (u₁ u₂ v₁ v₂ : kˣ),
      CategoryTheory.TwoPeriodicEndomorphism.determinant
          (CategoryTheory.TwoPeriodicEndomorphism.FourByFour.complex u₁ u₂ v₁ v₂)
          (CategoryTheory.TwoPeriodicEndomorphism.FourByFour.complex_isFiniteLength
            u₁ u₂ v₁ v₂)
          (CategoryTheory.TwoPeriodicEndomorphism.FourByFour.complex_acyclic
            u₁ u₂ v₁ v₂) =
        Units.map (IsLocalRing.residue k).toMonoidHom
          (-(u₁ * u₂) / (v₁ * v₂)))
