module

public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sober
public import stacks_project.Chap100.Definition_100_10_4_Reduced
public import stacks_project.Chap101.Definition_101_50_1_Integral

/-!
# Points, irreducible closed subsets, and integral closed substacks

On a decent algebraic stack with quasi-compact inertia morphism, the sober
space of points is in bijection with irreducible closed subsets via singleton
closures. Each irreducible closed subset carries a canonical integral closed
substack, namely its reduced induced structure, recovered uniquely up to
equality of `objectProperty`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The space of points of a decent algebraic stack with quasi-compact inertia
morphism is Kolmogorov. -/
instance instT0SpacePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    T0Space (Points X) :=
  sorry

/-- The space of points of a decent algebraic stack with quasi-compact inertia
morphism is quasi-sober. -/
instance instQuasiSoberPoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    QuasiSober (Points X) :=
  sorry

/-- The space of points of a decent algebraic stack with quasi-compact inertia
morphism is in bijection with its irreducible closed subsets. -/
noncomputable def pointsEquivIrreducibleCloseds {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    Points X ≃ IrreducibleCloseds (Points X) where
  toFun x :=
    IrreducibleCloseds.mk (closure {x}) isIrreducible_singleton.closure isClosed_closure
  invFun T := T.isIrreducible.genericPoint
  left_inv := sorry
  right_inv := sorry

/-- The bijection from points of a decent algebraic stack with quasi-compact
inertia morphism to irreducible closed subsets sends a point `x` to the
closure of `{x}`. -/
theorem coe_pointsEquivIrreducibleCloseds {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] (x : Points X) :
    (pointsEquivIrreducibleCloseds X x : Set (Points X)) = closure {x} :=
  sorry

/-- The inverse of `pointsEquivIrreducibleCloseds` sends an irreducible closed
subset to its generic point. -/
theorem isGenericPoint_pointsEquivIrreducibleCloseds_symm {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (T : IrreducibleCloseds (Points X)) :
    IsGenericPoint ((pointsEquivIrreducibleCloseds X).symm T) (T : Set (Points X)) :=
  sorry

namespace ClosedSubstack

/-- The closed substack of an algebraic stack associated to an irreducible
closed subset, given by the reduced induced structure. -/
noncomputable def ofIrreducibleClosed {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (T : IrreducibleCloseds (Points X)) : ClosedSubstack X :=
  (ClosedSubstackStructure.reduced
      (Closeds.mk (T : Set (Points X)) T.isClosed)).substack

/-- The reduced induced closed substack on an irreducible closed subset of a
decent algebraic stack with quasi-compact inertia morphism is integral. -/
instance instIsIntegral_ofIrreducibleClosed {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (T : IrreducibleCloseds (Points X)) :
    IsIntegral (ofIrreducibleClosed T).Y :=
  sorry

/-- The underlying point-set of the reduced induced closed substack is the
original irreducible closed subset. -/
theorem pointsSet_ofIrreducibleClosed {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (T : IrreducibleCloseds (Points X)) :
    (ofIrreducibleClosed T).pointsSet = (T : Set (Points X)) :=
  sorry

/-- The reduced induced closed substack on an irreducible closed subset of a
decent algebraic stack with quasi-compact inertia morphism is integral and has
that subset as its space of points. -/
theorem ofIrreducibleClosed_spec {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (T : IrreducibleCloseds (Points X)) :
    IsIntegral (ofIrreducibleClosed T).Y ∧
      (ofIrreducibleClosed T).pointsSet = (T : Set (Points X)) :=
  sorry

/-- The image of an integral closed substack in the ambient space of points is
irreducible. -/
theorem isIrreducible_pointsSet {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (Z : ClosedSubstack X) [IsIntegral Z.Y] :
    _root_.IsIrreducible Z.pointsSet :=
  sorry

/-- The irreducible closed subset of `Points X` associated to an integral
closed substack, namely its space of points. -/
noncomputable def irreducibleClosed {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (Z : ClosedSubstack X) [IsIntegral Z.Y] :
    IrreducibleCloseds (Points X) :=
  IrreducibleCloseds.mk Z.pointsSet (isIrreducible_pointsSet Z) (isClosed_pointsSet Z)

/-- The irreducible closed subset associated to an integral closed substack is
its underlying point-set. -/
theorem coe_irreducibleClosed {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (Z : ClosedSubstack X) [IsIntegral Z.Y] :
    (irreducibleClosed Z : Set (Points X)) = Z.pointsSet :=
  sorry

/-- An integral closed substack determines the same strictly full subcategory
as the reduced induced structure on its point-set. -/
theorem objectProperty_ofIrreducibleClosed {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] (Z : ClosedSubstack X)
    [IsIntegral Z.Y] :
    Z.objectProperty = (ofIrreducibleClosed (irreducibleClosed Z)).objectProperty :=
  sorry

end ClosedSubstack

end AlgebraicGeometry.AlgebraicStack
