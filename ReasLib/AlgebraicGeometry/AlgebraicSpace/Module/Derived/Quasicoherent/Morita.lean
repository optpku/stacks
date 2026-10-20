module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence

/-!
# Morita models of derived quasi-coherent categories

On a quasi-compact quasi-separated algebraic space, the derived category of
modules with quasi-coherent cohomology is equivalent to the derived category
of a cochain differential graded algebra with only finitely many nonzero
homology groups.
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
