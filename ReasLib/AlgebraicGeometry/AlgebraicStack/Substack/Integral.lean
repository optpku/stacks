module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Sober

/-!
# Integral closed substacks and irreducible closed subsets

Integral closed substacks are closed replete object properties with integral
restricted stacks. Support and reduced induced structure give inverse maps
between these substacks and irreducible closed subsets of the point space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- Integral closed substacks are closed replete object properties whose
literal restricted algebraic stacks are integral. -/
def IntegralClosedSubstacks (X : GroupoidsOver S) [AlgebraicStack X] :=
  {P : ObjectProperty X.total // ∃ hP : Substack.IsClosed X P,
    IsIntegral (Substack.closedCategory X P hP)}

namespace ClosedSubstackStructure

/-- The reduced induced stack on an irreducible closed subset of a decent
algebraic stack with quasi-compact inertia is integral. -/
instance instIsIntegral_reducedIrreducibleClosed [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]
    (T : IrreducibleCloseds (Points X)) :
    IsIntegral (reduced (Closeds.mk (T : Set (Points X)) T.isClosed)).Y :=
  sorry

end ClosedSubstackStructure

namespace IntegralClosedSubstacks

/-- The object property of an integral closed substack is closed. -/
theorem isClosed (Z : IntegralClosedSubstacks X) : Substack.IsClosed X Z.val := by
  obtain ⟨hZ, _⟩ := Z.property
  exact hZ

/-- The underlying stack of an integral closed substack is its literal
restricted category. -/
abbrev Y (Z : IntegralClosedSubstacks X) : GroupoidsOver S :=
  Substack.closedCategory X Z.val Z.isClosed

/-- The restricted stack of an integral closed substack is integral. -/
theorem isIntegral (Z : IntegralClosedSubstacks X) : IsIntegral Z.Y := by
  obtain ⟨hZ, hI⟩ := Z.property
  exact hI

/-- The support of an integral closed substack is the range of its inclusion
on ambient points. -/
def pointsSet (Z : IntegralClosedSubstacks X) : Set (Points X) :=
  Substack.pointsSet X Z.val Z.isClosed

/-- The support of an integral closed substack is closed. -/
theorem isClosed_pointsSet (Z : IntegralClosedSubstacks X) : IsClosed Z.pointsSet :=
  Points.isClosed_range_of_closedImmersion
    (Substack.closedInclusion X Z.val Z.isClosed)

/-- The support of an integral closed substack is irreducible. -/
theorem isIrreducible_pointsSet (Z : IntegralClosedSubstacks X) :
    _root_.IsIrreducible Z.pointsSet :=
  sorry

/-- An integral closed substack determines its irreducible closed support. -/
def irreducibleClosed (Z : IntegralClosedSubstacks X) : IrreducibleCloseds (Points X) :=
  IrreducibleCloseds.mk Z.pointsSet Z.isIrreducible_pointsSet Z.isClosed_pointsSet

/-- The underlying set of the irreducible closed support is the support itself. -/
theorem coe_irreducibleClosed (Z : IntegralClosedSubstacks X) :
    (irreducibleClosed Z : Set (Points X)) = Z.pointsSet := rfl

variable [IsDecent X] [QuasiCompact (forget.{u + 1, u, u, u + 1} X)]

/-- An irreducible closed subset determines the integral closed substack
defined by its reduced induced object property. -/
def ofIrreducibleClosed (T : IrreducibleCloseds (Points X)) :
    IntegralClosedSubstacks X :=
  ⟨Substack.reducedProperty (Closeds.mk (T : Set (Points X)) T.isClosed),
    Substack.reducedProperty_isClosed (Closeds.mk (T : Set (Points X)) T.isClosed),
    ClosedSubstackStructure.instIsIntegral_reducedIrreducibleClosed T⟩

/-- The support of the reduced induced integral closed substack is the
original irreducible closed subset. -/
theorem pointsSet_ofIrreducibleClosed (T : IrreducibleCloseds (Points X)) :
    (ofIrreducibleClosed T).pointsSet = (T : Set (Points X)) :=
  Substack.reducedProperty_pointsSet (Closeds.mk (T : Set (Points X)) T.isClosed)

/-- The reduced induced structure on the support of an integral closed
substack recovers that substack. -/
theorem ofIrreducibleClosed_irreducibleClosed (Z : IntegralClosedSubstacks X) :
    ofIrreducibleClosed (irreducibleClosed Z) = Z :=
  sorry

/-- The irreducible closed support of a reduced induced integral closed
substack is the original irreducible closed subset. -/
theorem irreducibleClosed_ofIrreducibleClosed (T : IrreducibleCloseds (Points X)) :
    irreducibleClosed (ofIrreducibleClosed T) = T := by
  apply IrreducibleCloseds.ext
  exact pointsSet_ofIrreducibleClosed T

/-- Integral closed substacks of a decent algebraic stack with quasi-compact
inertia correspond to irreducible closed subsets by support and reduced
induced structure. -/
def equivIrreducibleCloseds :
    IntegralClosedSubstacks X ≃ IrreducibleCloseds (Points X) where
  toFun := irreducibleClosed
  invFun := ofIrreducibleClosed
  left_inv := ofIrreducibleClosed_irreducibleClosed
  right_inv := irreducibleClosed_ofIrreducibleClosed

end IntegralClosedSubstacks

/-- For a decent algebraic stack with quasi-compact inertia, singleton closure
bijects points with irreducible closed subsets, and support bijects integral
closed substacks with those subsets. -/
theorem canonicalBijections (X : GroupoidsOver S) [AlgebraicStack X] [IsDecent X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] :
    Function.Bijective
      (irreducibleSetEquivPoints.toEquiv.symm : Points X ≃ IrreducibleCloseds (Points X)) ∧
    Function.Bijective
      (IntegralClosedSubstacks.irreducibleClosed :
        IntegralClosedSubstacks X → IrreducibleCloseds (Points X)) ∧
    (∀ x : Points X,
      (irreducibleSetEquivPoints.toEquiv.symm x : Set (Points X)) = closure {x}) ∧
    (∀ Z : IntegralClosedSubstacks X,
      (IntegralClosedSubstacks.irreducibleClosed Z : Set (Points X)) = Z.pointsSet) :=
  ⟨irreducibleSetEquivPoints.toEquiv.symm.bijective,
    IntegralClosedSubstacks.equivIrreducibleCloseds.bijective,
    coe_irreducibleEquivPoints_symm_apply,
    IntegralClosedSubstacks.coe_irreducibleClosed⟩

end AlgebraicGeometry.AlgebraicStack
