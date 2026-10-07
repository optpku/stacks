module

public import ReasLib.AlgebraicGeometry.CycleGroup

/-!
# Reindexing cycle groups

This file transports cycles between equal grading indices and records the resulting
compatibility with the underlying algebraic cycle.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- Transport a cycle group along an equality of its grading indices. -/
noncomputable def reindex {X : Scheme.{u}} (d : X → ℤ) {a b : ℤ} (h : a = b) :
    CycleGroup X d a →+ CycleGroup X d b :=
  AddEquiv.toAddMonoidHom
    (AddEquiv.cast (M := fun n : ℤ ↦ CycleGroup X d n) h)

/-- Transport along reflexivity is the identity additive homomorphism. -/
theorem reindex_refl {X : Scheme.{u}} (d : X → ℤ) (a : ℤ) :
    reindex d (rfl : a = a) = AddMonoidHom.id (CycleGroup X d a) := sorry

/-- Reindexing changes only the grading witness of a cycle, not its underlying algebraic
cycle. -/
theorem toAlgebraicCycle_reindex {X : Scheme.{u}} (d : X → ℤ) {a b : ℤ}
    (h : a = b) (alpha : CycleGroup X d a) :
    toAlgebraicCycle d b (reindex d h alpha) = toAlgebraicCycle d a alpha := sorry

end AlgebraicGeometry.CycleGroup
