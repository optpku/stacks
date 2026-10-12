/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.DerivedMorita.KernelEquivalence
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedCategory

universe u v

variable {R : Type u} [CommRing R]
variable (A B : CochainDGAlgebra.{u, v} R)
variable (hA : A.IsConcentratedInDegreeZero) (hB : B.IsKFlat)
variable (e : RLinear.TriangulatedEquivalence R
  (DifferentialGradedModule.Derived.Category.{u, v} A)
  (DifferentialGradedModule.Derived.Category.{u, v} B))

/- Proposition 22.37.6 (09SA): an `R`-linear triangulated equivalence between the derived
categories of `A` and `B`, with `A` concentrated in degree zero and `B` K-flat, admits a
differential graded `(A, B)`-bimodule satisfying the compact-generator and shifted self-Hom
conditions of Lemma 22.37.2. -/
@[stacks 09SA] #check
  (CochainDGAlgebra.DerivedMorita.exists_bimodule A B hA hB e :
    ∃ (N : DifferentialGradedBimodule.{u, v, v, v} A B)
      (_ : e.functor.obj (DifferentialGradedModule.Derived.regularObject A) ≅
        N.rightDerivedObject),
      N.IsMoritaKernel)

/- The comparison in condition (3) is the canonical map induced by the left action. -/
#check @DifferentialGradedBimodule.selfExtMap
#check @DifferentialGradedBimodule.HasSelfExtComparisonFor
#check @DifferentialGradedBimodule.HasSelfExtComparison
#check @DifferentialGradedBimodule.IsMoritaKernelFor
#check @DifferentialGradedBimodule.IsMoritaKernel

/- The equivalence criterion retains the Morita-kernel certificate for direct tensor reuse. -/
#check
  (CochainDGAlgebra.DerivedMorita.nonempty_equivalence_iff_exists_kernel
      A B hA hB :
    Nonempty (RLinear.TriangulatedEquivalence R
      (DifferentialGradedModule.Derived.Category.{u, v} A)
      (DifferentialGradedModule.Derived.Category.{u, v} B)) ↔
      ∃ N : DifferentialGradedBimodule.{u, v, v, v} A B, N.IsMoritaKernel)

/- The reusable categorical conclusion is the compact-generator equivalence criterion. -/
#check @CategoryTheory.Functor.IsEquivalence.ofCompactGenerator
