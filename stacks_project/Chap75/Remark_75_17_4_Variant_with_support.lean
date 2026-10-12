/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Remark_75_17_4_Variant_with_support_Morita
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits
open TopologicalSpace

universe u

/- Remark 75.17.4 (Variant with support): for a scheme `S`, a quasi-compact
quasi-separated algebraic space `X` over `S`, and a closed subset `T ⊆ |X|`
with quasi-compact complement, there is an integral cochain differential graded
algebra whose homology is nonzero in only finitely many degrees and whose
derived category is linearly triangulated equivalent to `D_QCoh,T(𝒪_X)`. -/
@[stacks 0DK8] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.exists_dgAlgebra_equivalence :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (T : Closeds (Points X)),
      QuasiCompact (OpenSubspace.ofOpensι T.compl) →
      ∃ E : CochainDGAlgebra.{0, u} ℤ,
        Set.Finite {i | ¬ IsZero (E.homology i)} ∧
          Nonempty (RLinear.TriangulatedEquivalence ℤ
            (DifferentialGradedModule.Derived.Category.{0, u} E)
            (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn X (T : Set (Points X)))))
