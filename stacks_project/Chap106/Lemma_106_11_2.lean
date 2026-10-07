module

public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_8_1_Noetherian
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap106.Lemma_106_11_2_DvrUniqueness

/-!
# Noetherian valuative criterion for separatedness of algebraic stacks

A locally of finite type quasi-separated morphism of algebraic stacks into a
locally Noetherian target is separated as soon as every DVR valuative 2-square
has dotted-arrow category empty or a setoid with exactly one isomorphism class.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Separated

/-- Lemma 106.11.2: if `f : X ⟶ Y` is a morphism of algebraic stacks over a
scheme `S`, `Y` is locally Noetherian, `f` is locally of finite type and
quasi-separated, and every 2-commutative valuative square `Spec(K) ⟶ X` over
`Spec(A) ⟶ Y` with `A` a discrete valuation ring and `K` its field of fractions
has dotted-arrow category either empty or a setoid with exactly one isomorphism
class, then `f` is separated. -/
@[stacks 0E80]
instance of_dvrUniqueness {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [QuasiSeparated f]
    [ValuativeCriterion.DVR.Uniqueness f] : Separated f :=
  sorry

end Separated

end AlgebraicGeometry.AlgebraicStack
