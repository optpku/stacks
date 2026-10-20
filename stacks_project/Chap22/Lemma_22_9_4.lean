module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.MappingConeComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R}
variable (S : CategoryTheory.ShortComplex (DifferentialGradedModule.{u, v} A))
variable (sigma : DifferentialGradedModule.ShortComplex.GradedSplitting S)

/- Lemma 22.9.4 (1) (09KF): an associated triangle of an admissible DG-module short exact
sequence is isomorphic to the mapping-cone triangle of its first map, through the identity on the
first two vertices and the explicit projection `mappingCone S.f ⟶ S.X₃` on the third. -/
@[stacks 09KF]
#check (DifferentialGradedModule.ShortComplex.mappingConeTriangleIso S sigma :
  DifferentialGradedModule.MappingCone.triangleK S.f ≅
    DifferentialGradedModule.ShortComplex.associatedTriangleK S sigma)

/- The comparison and inverse representatives are explicit DG-module maps. -/
#check @DifferentialGradedModule.ShortComplex.coneProjection
#check @DifferentialGradedModule.ShortComplex.coneSection
#check @DifferentialGradedModule.ShortComplex.coneComparisonIsoK

variable {K L : DifferentialGradedModule.{u, v} A}
variable (f : K ⟶ L)

/- Lemma 22.9.4 (2) (09KF): the canonical admissibly monic replacement of any DG-module map has
a cone triangle explicitly isomorphic to the original mapping-cone triangle. -/
@[stacks 09KF]
#check (DifferentialGradedModule.SplitMonoFactorization.triangleIso f :
  DifferentialGradedModule.MappingCone.triangleK
      (DifferentialGradedModule.SplitMonoFactorization.inclusion f) ≅
    DifferentialGradedModule.MappingCone.triangleK f)

/- The source cone triangle of the replacement comparison is associated to an admissible quotient
row. -/
#check @DifferentialGradedModule.SplitMonoFactorization.triangle_hasAssociatedConeRow

/- More generally, admissible monomorphisms admit quotient rows whose associated triangles are
their standard mapping-cone triangles. -/
#check @DifferentialGradedModule.ShortComplex.hasAssociatedConeRow_of_admissibleMono
