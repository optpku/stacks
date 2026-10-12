/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.Affineness
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 51.4.8 -/
@[stacks 0DXD] #check
  (Ideal.LocalCohomology.idealComplementOpens_isAffine_of_dimension_eq_one :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG),
      Ideal.LocalCohomology.dimension I hI = 1 →
        Nonempty (AlgebraicGeometry.Scheme.Modules.idealComplementOpens I) ∧
          AlgebraicGeometry.IsAffineOpen
            (AlgebraicGeometry.Scheme.Modules.idealComplementOpens I))
