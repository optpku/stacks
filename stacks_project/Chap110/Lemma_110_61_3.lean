module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap110.Lemma_110_61_3_Pushforward

/-!
# Derived pushforward of quasi-coherent modules need not exist unbounded
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicStack GroupoidsOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 110.61.3: a quasi-compact and quasi-separated morphism `f : X ⟶ Y` of
algebraic stacks need not induce `Rf_* : DerivedQCoh X ⥤ DerivedQCoh Y`. This is
the failure of unbounded fppf-module derived pushforward to preserve
`D_{LQCoh^{fbc}}`, the ambient of `DerivedQCoh`. -/
@[stacks 07DD]
theorem not_forall_mapsDerivedLQCohFbc :
    ¬ ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
        [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
        [QuasiCompact f] [QuasiSeparated f], mapsDerivedLQCohFbc f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
