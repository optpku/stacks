/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Proper closed subsets of algebraic spaces over a base

Properness of a closed subset is expressed by a proper closed immersion whose
point image is the prescribed subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset

/-- A closed subset `T` of `Points X` is proper over `Y` along `f : X ⟶ Y` when it is
the point image of a closed immersion that is proper over `Y`. -/
def ProperOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Closeds (Points X)) : Prop :=
  ∃ (Z : AlgebraicSpace S) (i : Z ⟶ X),
    IsClosedImmersion i ∧ Set.range (Points.map i) = T.carrier ∧ Proper (i ≫ f)

namespace ProperOver

/-- A closed subset contained in a proper closed subset is proper over the same base
along a locally-of-finite-type morphism. -/
theorem mono {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [LocallyOfFiniteType f] {T' T : Closeds (Points X)} (h : T' ≤ T)
    (hT : ProperOver f T) : ProperOver f T' := sorry

end ProperOver

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset
