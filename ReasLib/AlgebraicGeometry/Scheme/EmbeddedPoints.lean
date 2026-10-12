/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.EmbeddedPoints

/-!
# Embedded points of schemes

This leaf specializes embedded associated points to the structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open Set TopologicalSpace

variable (X : Scheme.{u})

/-- A point `x` is an embedded point of `X` when it is embedded associated for the structure
sheaf. -/
def embeddedPoint (x : X) : Prop :=
  Scheme.Modules.embeddedAssociatedAt (SheafOfModules.unit X.ringCatSheaf : X.Modules) x

/-- Unfold an embedded point into the associated-point and specialization
conditions. -/
theorem embeddedPoint_iff (x : X) :
    X.embeddedPoint x ↔
      x ∈ X.associatedPoints ∧
        ∃ y : X, y ∈ X.associatedPoints ∧ y ≠ x ∧ y ⤳ x := sorry

/-- An embedded point is an associated point. -/
theorem embeddedPoint.mem_associatedPoints {x : X} (hx : X.embeddedPoint x) :
    x ∈ X.associatedPoints := sorry

/-- An embedded point is the specialization of a distinct associated point. -/
theorem embeddedPoint.exists_specializing_associated {x : X}
    (hx : X.embeddedPoint x) :
    ∃ y : X, y ∈ X.associatedPoints ∧ y ≠ x ∧ y ⤳ x := sorry

/-- The set of embedded points of `X`. -/
def embeddedPoints : Set X :=
  X.embeddedPoint

/-- Membership in `embeddedPoints` is the embedded-point predicate. -/
theorem mem_embeddedPoints_iff (x : X) :
    x ∈ X.embeddedPoints ↔ X.embeddedPoint x := sorry

/-- A scheme has no embedded points exactly when none of its points is
embedded. -/
theorem embeddedPoints_eq_empty_iff :
    X.embeddedPoints = (∅ : Set X) ↔ ∀ x : X, ¬ X.embeddedPoint x := sorry

/-- An embedded component is an irreducible closed subset that is the closure of an embedded
point. -/
def isEmbeddedComponent (Z : TopologicalSpace.IrreducibleCloseds X) : Prop :=
  ∃ x : X, X.embeddedPoint x ∧ (Z : Set X) = closure ({x} : Set X)

/-- Unfold `isEmbeddedComponent` into its embedded-point presentation. -/
theorem isEmbeddedComponent_iff (Z : TopologicalSpace.IrreducibleCloseds X) :
    X.isEmbeddedComponent Z ↔
      ∃ x : X, X.embeddedPoint x ∧ (Z : Set X) = closure ({x} : Set X) := sorry

/-- An embedded component is the closure of an embedded point. -/
theorem isEmbeddedComponent.exists_embeddedPoint
    {Z : TopologicalSpace.IrreducibleCloseds X} (hZ : X.isEmbeddedComponent Z) :
    ∃ x : X, X.embeddedPoint x ∧ (Z : Set X) = closure ({x} : Set X) := sorry

end AlgebraicGeometry.Scheme
