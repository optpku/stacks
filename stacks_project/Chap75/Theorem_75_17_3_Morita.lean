/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh

/-!
# Morita models of derived quasi-coherent categories

On a quasi-compact quasi-separated algebraic space, the derived category of
modules with quasi-coherent cohomology is equivalent to the derived category of
a cochain differential graded algebra with only finitely many nonzero homology
groups.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace DerivedQCoh

/-- Every quasi-compact quasi-separated algebraic space has an integral cochain
differential graded algebra with only finitely many nonzero homology objects
whose derived module category is ℤ-linearly triangulated equivalent to the
derived category of modules with quasicoherent cohomology. -/
theorem exists_dgAlgebra_equivalence {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    ∃ E : CochainDGAlgebra.{0, u} ℤ,
      Set.Finite {i | ¬ IsZero (E.homology i)} ∧
        Nonempty (RLinear.TriangulatedEquivalence ℤ
          (DifferentialGradedModule.Derived.Category.{0, u} E)
          (DerivedQCoh X)) := sorry

end DerivedQCoh

end AlgebraicGeometry.AlgebraicSpace
