module

public import stacks_project.Chap75.Theorem_75_17_3_Morita
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Theorem 75.17.3: for a scheme `S` and a quasi-compact quasi-separated algebraic
space `X` over `S`, there is an integral cochain differential graded algebra whose
homology is nonzero in only finitely many degrees and whose derived category is
linearly triangulated equivalent to `D_QCoh(𝒪_X)`. -/
@[stacks 09MC] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.exists_dgAlgebra_equivalence :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X],
      ∃ E : CochainDGAlgebra.{0, u} ℤ,
        Set.Finite {i | ¬ IsZero (E.homology i)} ∧
          Nonempty (RLinear.TriangulatedEquivalence ℤ
            (DifferentialGradedModule.Derived.Category.{0, u} E)
            (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X)))
