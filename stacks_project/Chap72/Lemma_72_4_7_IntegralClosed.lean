module

public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sober
public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap68.Lemma_68_12_3
public import stacks_project.Chap68.Proposition_68_12_4
public import stacks_project.Chap72.Definition_72_4_1_Integral

/-!
# Points, irreducible closed subsets, and integral closed subspaces

On a decent algebraic space, the sober space of points is in bijection with
irreducible closed subsets via singleton closures. Each irreducible closed
subset carries a canonical integral closed subspace, namely its reduced
induced structure, recovered uniquely up to a morphism over the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The space of points of a decent algebraic space is in bijection with its
irreducible closed subsets. -/
noncomputable def pointsEquivIrreducibleCloseds {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] : Points X ≃ IrreducibleCloseds (Points X) where
  toFun x :=
    IrreducibleCloseds.mk (closure {x}) isIrreducible_singleton.closure isClosed_closure
  invFun T := T.isIrreducible.genericPoint
  left_inv := sorry
  right_inv := sorry

/-- The bijection from points of a decent algebraic space to irreducible closed
subsets sends a point `x` to the closure of `{x}`. -/
theorem coe_pointsEquivIrreducibleCloseds {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) :
    (pointsEquivIrreducibleCloseds X x : Set (Points X)) = closure {x} :=
  sorry

/-- The inverse of `pointsEquivIrreducibleCloseds` sends an irreducible closed
subset to its generic point. -/
theorem isGenericPoint_pointsEquivIrreducibleCloseds_symm {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (T : IrreducibleCloseds (Points X)) :
    IsGenericPoint ((pointsEquivIrreducibleCloseds X).symm T) (T : Set (Points X)) :=
  sorry

namespace ClosedSubspace

/-- The integral closed subspace of a decent algebraic space associated to an
irreducible closed subset, given by the reduced induced structure. -/
noncomputable def ofIrreducibleClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (T : IrreducibleCloseds (Points X)) : ClosedSubspace X :=
  (ClosedSubspaceStructure.reduced (Closeds.mk (T : Set (Points X)) T.isClosed)).subspace

/-- The reduced induced closed subspace on an irreducible closed subset of a
decent algebraic space is integral. -/
instance instIsIntegral_ofIrreducibleClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (T : IrreducibleCloseds (Points X)) :
    IsIntegral (ofIrreducibleClosed T).X :=
  sorry

/-- The underlying point-set of the reduced induced integral closed subspace is
the original irreducible closed subset. -/
theorem pointsSet_ofIrreducibleClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (T : IrreducibleCloseds (Points X)) :
    (ofIrreducibleClosed T).pointsSet = (T : Set (Points X)) :=
  sorry

/-- The reduced induced closed subspace on an irreducible closed subset is
integral and has that subset as its space of points. -/
theorem ofIrreducibleClosed_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (T : IrreducibleCloseds (Points X)) :
    IsIntegral (ofIrreducibleClosed T).X ∧
      (ofIrreducibleClosed T).pointsSet = (T : Set (Points X)) :=
  sorry

/-- The image of an integral closed subspace in the ambient space of points is
irreducible. -/
theorem isIrreducible_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsIntegral Z.X] :
    _root_.IsIrreducible Z.pointsSet :=
  sorry

/-- The irreducible closed subset of `Points X` associated to an integral closed
subspace, namely its space of points. -/
noncomputable def irreducibleClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsIntegral Z.X] : IrreducibleCloseds (Points X) :=
  IrreducibleCloseds.mk Z.pointsSet (isIrreducible_pointsSet Z) (isClosed_pointsSet Z)

/-- The irreducible closed subset associated to an integral closed subspace is
its underlying point-set. -/
theorem coe_irreducibleClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsIntegral Z.X] :
    (irreducibleClosed Z : Set (Points X)) = Z.pointsSet :=
  sorry

/-- An integral closed subspace of a decent algebraic space admits a unique
morphism over `X` to the reduced induced structure on its point-set. -/
theorem existsUnique_hom_ofIrreducibleClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (Z : ClosedSubspace X) [IsIntegral Z.X] :
    ∃! f : Z.X ⟶ (ofIrreducibleClosed (irreducibleClosed Z)).X,
      f ≫ (ofIrreducibleClosed (irreducibleClosed Z)).ι = Z.ι :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
