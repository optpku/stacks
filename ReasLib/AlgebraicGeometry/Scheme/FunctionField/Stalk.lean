/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Stalks inside a scheme's function field

This file packages the image of a stalk in the function field of an integral scheme and compares
the images attached to generic points of irreducible closed subsets.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsIntegral X]

/-- The image of the canonical map from the stalk at a point to the function field. -/
noncomputable abbrev stalkInFunctionField (x : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range

/-- The image in the function field of the stalk at the generic point of an irreducible closed
subset. -/
noncomputable abbrev genericPointStalkInFunctionField
    (Z : IrreducibleCloseds X) : Subring X.functionField :=
  X.stalkInFunctionField Z.isIrreducible.genericPoint

/-- An element of the function field belongs to the image of the stalk at `x` exactly when it is
the image of an element of that stalk. -/
@[simp] theorem mem_stalkInFunctionField_iff (x : X) (f : X.functionField) :
    f ∈ X.stalkInFunctionField x ↔
      ∃ a : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField a = f :=
  Iff.rfl

/-- An element of the function field belongs to the generic-point stalk image exactly when it is
the image of an element of the corresponding stalk. -/
@[simp] theorem mem_genericPointStalkInFunctionField_iff
    (Z : IrreducibleCloseds X) (f : X.functionField) :
    f ∈ X.genericPointStalkInFunctionField Z ↔
      ∃ a : X.presheaf.stalk Z.isIrreducible.genericPoint,
        algebraMap (X.presheaf.stalk Z.isIrreducible.genericPoint) X.functionField a = f := by
  simpa [genericPointStalkInFunctionField] using
    X.mem_stalkInFunctionField_iff Z.isIrreducible.genericPoint f

variable [X.IsSeparated]

/-- If one irreducible closed subset of an integral separated scheme is not contained in another,
then the image in the function field of the first generic-point stalk is not contained in the
image of the second. -/
theorem genericPointStalkRange_not_subset_of_not_subset
    (Z₁ Z₂ : IrreducibleCloseds X) (hnot : ¬ (Z₁ : Set X) ⊆ Z₂) :
    ¬ X.genericPointStalkInFunctionField Z₁ ≤ X.genericPointStalkInFunctionField Z₂ := sorry

/-- A closed point outside an irreducible closed subset has a regular function on some
neighborhood whose germ does not belong to the generic-point stalk image of that subset. -/
theorem exists_regularFunction_near_closedPoint_not_mem_genericPointStalk
    (Z₂ : IrreducibleCloseds X) (x : X) (hxClosed : IsClosed ({x} : Set X))
    (hxNotMem : x ∉ (Z₂ : Set X)) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (f : Γ(X, U)),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hxU f) ∉
        X.genericPointStalkInFunctionField Z₂ := sorry

end AlgebraicGeometry.Scheme
