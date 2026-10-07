module

public import stacks_project.Chap78.Definition_78_8_1_Action

/-!
# Trivial actions of group algebraic spaces

The trivial action of a group algebraic space `G` over `B` is the module object
structure on the terminal object of `Over B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- The trivial action of a group algebraic space `G` on the terminal object of
`Over B`. -/
def trivialAction {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    Action G :=
  Mod.trivialAction G.toMon (𝟙_ (Over B))

/-- The underlying object of `trivialAction G` is the terminal algebraic space over
`B`. -/
theorem trivialAction_X {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) : (trivialAction G).X = 𝟙_ (Over B) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
