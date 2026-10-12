/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Definition_101_37_1_FiniteType
public import stacks_project.Chap101.Definition_101_27_1_FinitePresentation

/-!
# Locally Noetherian targets upgrade finite type to finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.27.5 (1): A morphism of algebraic stacks which is locally of finite
type, with locally Noetherian target, is locally of finite presentation. -/
@[stacks 0DQJ]
instance locallyOfFinitePresentation_of_locallyOfFiniteType {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation f :=
  sorry

/-- Lemma 101.27.5 (2): A morphism of algebraic stacks which is of finite type
and quasi-separated, with locally Noetherian target, is of finite
presentation. -/
@[stacks 0DQJ]
instance finitePresentation_of_finiteType {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [FiniteType f] [QuasiSeparated f] :
    FinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
