module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.DenseOpen
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extending local finite presentation from a dense open

Local finite presentation of a flat morphism locally of finite type can be extended from a
retrocompact scheme-theoretically dense open of the target.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyOfFinitePresentation

/-- A flat morphism locally of finite type is locally of finite presentation if its restriction
to a retrocompact scheme-theoretically dense open is locally of finite presentation. -/
@[stacks 081P]
theorem of_restrict_of_flat {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [Flat f] (U : S.Opens)
    (hU_retrocompact : IsRetrocompact (U : Set S))
    (hU_dense : schemeTheoreticallyDense U)
    [LocallyOfFinitePresentation (f ∣_ U)] :
    LocallyOfFinitePresentation f := sorry

end AlgebraicGeometry.LocallyOfFinitePresentation
