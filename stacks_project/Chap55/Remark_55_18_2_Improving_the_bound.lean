module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Curve.SemistableReduction.Existence
import ReasLib.AlgebraicGeometry.Curve.SemistableReduction.Bound

open AlgebraicGeometry

universe u

/-
Remark 55.18.2 (Improving the bound)

Results in the literature suggest improving the bound in Theorem 55.18.1. In [DM],
semistable reduction of a curve and its Jacobian are equivalent when the residue field
is perfect; the extension of this comparison to general residue fields is tentative.
For an abelian variety, trivial Galois action on the ℓ-torsion implies semistable
reduction for a prime ℓ ≥ 3 distinct from the residue characteristic. This suggests
choosing ℓ = 5 in formula (55.18.0.1) for B_g, but the source postpones a precise
statement and proof. The checks below record the established bound and its formula,
not the suggested improvement.
-/
@[stacks 0CEK] #check (AlgebraicGeometry.Curve.semistableReduction_genusGeTwo :
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus : g = SchemeOverField.genus C
      (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections)
    (h_g : 2 ≤ g),
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'),
      Scheme.Hom.hasSemistableReductionAtMaximal R K K'
          (FieldExtension.Over.baseChange K K' C) ∧
        Module.finrank K K' ≤ semistableReductionBound g)

#check (semistableReductionBound_eq :
  ∀ (g : ℕ) (h_genus : 2 ≤ g),
    semistableReductionBound g =
      (2 * g - 2) * Nat.factorial (semistableReductionPrime g ^ (2 * g)))
