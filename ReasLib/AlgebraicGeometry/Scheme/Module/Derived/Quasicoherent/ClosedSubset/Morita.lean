/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Morita
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Perfect.Generation

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn

/-- For a quasi-compact quasi-separated scheme and a closed subset with quasi-compact
complement, there is an integral cochain differential graded algebra with finitely many
nonzero homology objects whose derived module category is linearly triangulated equivalent
to the derived category of quasi-coherent complexes supported on that subset. -/
theorem exists_dgAlgebra_equivalence {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (T : TopologicalSpace.Closeds X)
    (hT : IsCompact (T.compl : Set X)) :
    ∃ E : CochainDGAlgebra.{0, u} ℤ,
      Set.Finite {i : ℤ | ¬ IsZero (E.homology i)} ∧
        Nonempty (RLinear.TriangulatedEquivalence ℤ
          (DifferentialGradedModule.Derived.Category.{0, u} E) (SupportedOn X T)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn
