module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 51.4.4: the cohomological dimension of the sum of two finitely generated ideals
is at most the sum of their cohomological dimensions. -/
@[stacks 0ECP] #check (Ideal.LocalCohomology.dimension_sup_le :
  ∀ {A : Type u} [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG),
    Ideal.LocalCohomology.dimension (I ⊔ J) (Submodule.FG.sup hI hJ) ≤
      Ideal.LocalCohomology.dimension I hI + Ideal.LocalCohomology.dimension J hJ)
