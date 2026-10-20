module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField.Dimension
import StacksCheckRecall

/-!
# Dimension of the stabilizer of a groupoid on a field

In Situation 79.9.2, if the source and target maps are locally of finite type,
then the algebraic-space dimension of the arrow space equals that of the
stabilizer group algebraic space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/- Lemma 79.9.11: in Situation 79.9.2, if `G.s` and `G.t` are locally of finite
type, then `dimension G.R.left = dimension G.stabilizer.X.left.left`. Here
`G.stabilizer` is the stabilizer group algebraic space given by the diagonal
pullback of `j = prod.lift G.t G.s`, i.e. the fibre product
`Spec (.of k) ×_{Δ, Spec (.of k) ×_B Spec (.of k), t × s} R`. -/
@[stacks 06FF] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.dimension_eq_stabilizer :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left],
    dimension G.R.left = dimension G.stabilizer.X.left.left)

/- In Situation 79.9.2, if `G.s` and `G.t` are locally of finite type, then the
dimension of `G.R` at any point equals the dimension of the stabilizer group
algebraic space. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.dimensionAt_eq_dimension_stabilizer :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left),
    dimensionAt r = dimension G.stabilizer.X.left.left)

end AlgebraicGeometry.GroupoidAlgebraicSpace
