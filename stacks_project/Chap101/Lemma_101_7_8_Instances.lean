/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_8_1_Noetherian

/-!
# Quasi-compact and quasi-separated morphisms from stack properties

A morphism of algebraic stacks out of a quasi-compact source into a
quasi-separated target is quasi-compact. A morphism between quasi-separated
algebraic stacks is quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace QuasiCompact

/-- A morphism of algebraic stacks from a quasi-compact source to a
quasi-separated target is quasi-compact. -/
instance (priority := low) of_isQuasiCompact {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiCompact X] [IsQuasiSeparated Y] : QuasiCompact f :=
  sorry

end QuasiCompact

namespace QuasiSeparated

/-- A morphism of algebraic stacks between quasi-separated algebraic stacks is
quasi-separated. -/
instance (priority := low) of_isQuasiSeparated {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiSeparated X] [IsQuasiSeparated Y] : QuasiSeparated f :=
  sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicStack
