/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Support.Generation

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
    (hT : IsCompact (T.compl : Set (Points X))) :
    ∃ E : CochainDGAlgebra.{0, u} ℤ,
      Set.Finite {i | ¬ IsZero (E.homology i)} ∧
        Nonempty (RLinear.TriangulatedEquivalence ℤ
          (DifferentialGradedModule.Derived.Category.{0, u} E)
          (SupportedOn X (T : Set (Points X)))) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn
