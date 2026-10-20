module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Every quasi-compact scheme contains a dense open subscheme that is separated. -/
theorem exists_dense_open_isSeparated {X : Scheme.{u}} [CompactSpace X] :
    ∃ U : X.Opens, U.toScheme.IsSeparated ∧ Dense (U : Set X) := sorry

/-- There exists a quasi-compact and quasi-separated scheme with no dense open subscheme that is both quasi-compact and separated. -/
theorem exists_qcqs_no_separated_quasiCompact_dense_open :
    ∃ (X : Scheme.{u}),
      CompactSpace X ∧
        QuasiSeparatedSpace X ∧
          ¬ ∃ (U : X.Opens),
              Dense (U : Set X) ∧ IsCompact (U : Set X) ∧ U.toScheme.IsSeparated := sorry

end AlgebraicGeometry.Scheme
