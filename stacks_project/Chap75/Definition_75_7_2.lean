module

public import stacks_project.Chap75.Lemma_75_7_3_ProperOver
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
variable (T : TopologicalSpace.Closeds (Points X))

/- Definition 75.7.2: the equivalent conditions of Lemma 75.7.1 /
`isProperOver_tfae` define when the closed subset `T` of `Points X` is proper
over `Y` along a locally of finite type morphism `f : X ⟶ Y` of algebraic
spaces over the scheme `S`; equivalently, `IsProperOver f T` says that the
reduced induced closed subspace of `T` is proper over `Y`. -/
@[stacks 0CZD] #check (IsProperOver f T : Prop)

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset
