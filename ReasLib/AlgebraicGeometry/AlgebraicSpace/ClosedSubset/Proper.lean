module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure

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

/-- Along a locally of finite type morphism, properness is equivalent for the reduced
induced structure on a closed subset, some closed-subspace structure on that subset,
and every such structure. -/
theorem isProperOver_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (T : Closeds (Points X)) :
    List.TFAE [
      Proper ((ClosedSubspaceStructure.reduced T).ι ≫ f),
      ∃ Z : ClosedSubspaceStructure T, Proper (Z.ι ≫ f),
      ∀ Z : ClosedSubspaceStructure T, Proper (Z.ι ≫ f)] :=
  sorry

/-- Along a locally of finite type morphism, the reduced induced structure on a closed
subset is proper over the target if and only if some closed-subspace structure is. -/
theorem isProperOver_iff_exists {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (T : Closeds (Points X)) :
    Proper ((ClosedSubspaceStructure.reduced T).ι ≫ f) ↔
      ∃ Z : ClosedSubspaceStructure T, Proper (Z.ι ≫ f) :=
  (isProperOver_tfae f T).out 0 1

/-- Along a locally of finite type morphism, the reduced induced structure on a closed
subset is proper over the target if and only if every closed-subspace structure is. -/
theorem isProperOver_iff_forall {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (T : Closeds (Points X)) :
    Proper ((ClosedSubspaceStructure.reduced T).ι ≫ f) ↔
      ∀ Z : ClosedSubspaceStructure T, Proper (Z.ι ≫ f) :=
  (isProperOver_tfae f T).out 0 2

/-- Along a locally of finite type morphism, some closed-subspace structure on a closed
subset is proper over the target if and only if every such structure is. -/
theorem isProperOver_exists_iff_forall {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (T : Closeds (Points X)) :
    (∃ Z : ClosedSubspaceStructure T, Proper (Z.ι ≫ f)) ↔
      ∀ Z : ClosedSubspaceStructure T, Proper (Z.ι ≫ f) :=
  (isProperOver_tfae f T).out 1 2

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset
