module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap75.Remark_75_16_4_Generation
public import stacks_project.Chap81.Lemma_81_10_10_SupportedOn

/-!
# Morita models of supported derived quasi-coherent categories

On a quasi-compact quasi-separated algebraic space, the derived category of
quasi-coherent complexes supported on a closed subset with quasi-compact
complement is equivalent to the derived category of a cochain differential
graded algebra with only finitely many nonzero homology groups.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn

/-- Every quasi-compact quasi-separated algebraic space has, for each closed
subset of points with quasi-compact complement, an integral cochain differential
graded algebra with only finitely many nonzero homology objects whose derived
module category is ℤ-linearly triangulated equivalent to the derived category of
modules with quasicoherent cohomology supported on that subset. -/
theorem exists_dgAlgebra_equivalence {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl)) :
    ∃ E : CochainDGAlgebra.{0, u} ℤ,
      Set.Finite {i | ¬ IsZero (E.homology i)} ∧
        Nonempty (RLinear.TriangulatedEquivalence ℤ
          (DifferentialGradedModule.Derived.Category.{0, u} E)
          (SupportedOn X (T : Set (Points X)))) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn
