/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
variable (hS : DifferentialGradedModule.IsAdmissibleShortExact S)

/- Lemma 22.9.2 (09KC): for an admissible DG-module short exact sequence, the triangle
`(M[-1], K, L, delta[-1], alpha, beta)` is isomorphic in the intrinsic DG homotopy category to
the mapping-cone triangle of the explicitly deshifted connecting map. -/
@[stacks 09KC]
#check (DifferentialGradedModule.ShortComplex.exists_deshiftedTriangleIso_of_admissible S hS :
  ∃ sigma : DifferentialGradedModule.ShortComplex.GradedSplitting S,
    Nonempty
      (DifferentialGradedModule.ShortComplex.deshiftedTriangleK S sigma ≅
        DifferentialGradedModule.MappingCone.triangleK
          (DifferentialGradedModule.ShortComplex.deshiftConnectingHom S sigma)))

/- Once a graded splitting is supplied, the comparison is available without any witness choice. -/
#check @DifferentialGradedModule.ShortComplex.nonempty_deshiftedTriangleIso

/- The deshifted connecting map and triangle remain available as explicit data. -/
#check @DifferentialGradedModule.ShortComplex.deshiftConnectingHom
#check @DifferentialGradedModule.ShortComplex.deshiftedTriangleK
