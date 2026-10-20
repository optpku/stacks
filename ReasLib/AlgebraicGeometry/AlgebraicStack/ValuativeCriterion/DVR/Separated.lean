module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DVR
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.DVR.UniquenessAlong
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

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

/-- If `f : X ⟶ Y` is a morphism of algebraic stacks over a
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

/-- Let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of algebraic
stacks over a scheme `S`. Assume that `Y` is locally Noetherian, that `f` is
locally of finite type and quasi-separated, that `h` is of finite type, and
that the image of `|h| : |U| ⟶ |X|` is dense in `|X|`. If every 2-commutative
diagram `Spec(K) ⟶ U ⟶ X` over `Spec(A) ⟶ Y` with `A` a discrete valuation
ring and `K` its field of fractions has dotted-arrow category either empty or
a setoid with exactly one isomorphism class, then `f` is separated. -/
@[stacks 0E95]
theorem of_uniquenessAlong {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (h : U ⟶ X)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [QuasiSeparated f] [FiniteType h]
    (h_dense : DenseRange (Points.map h))
    (h_uniqueness : ValuativeCriterion.DVR.Along.Uniqueness h f) :
    Separated f :=
  sorry

end Separated

end AlgebraicGeometry.AlgebraicStack
