/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Generation
public import ReasLib.CategoryTheory.Pretriangulated.Functor.RLinearEquivalence

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Every quasi-compact quasi-separated scheme has an integral cochain differential graded
algebra with only finitely many nonzero homology objects whose derived module category is
ℤ-linearly triangulated equivalent to the derived category of modules with quasicoherent
cohomology. -/
theorem exists_dgAlgebra_equivalence {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] :
    ∃ E : CochainDGAlgebra.{0, u} ℤ,
      Set.Finite {i : ℤ | ¬ IsZero (E.homology i)} ∧
        Nonempty (RLinear.TriangulatedEquivalence ℤ
          (DifferentialGradedModule.Derived.Category.{0, u} E)
          (Scheme.ModuleDerived.Quasicoherent X)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
