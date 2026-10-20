module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.HomologyAlgebra

/-!
# Representatives of nonnegative homology classes

This file exposes reusable choices of cycle representatives for the canonical Mathlib homology
modules of a chain DGA. It also provides finite-support assembly maps from closed even chain
values to the corresponding even homology classes.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DirectSum

universe u v

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

/-- A selected cycle representing a class in canonical nonnegative homology. -/
@[stacks 09PK "infrastructure: cycle representatives for homology"]
noncomputable def homologyCycleRepresentative (A : ChainDGAlgebra.{u, v} R) (n : ℕ) :
    A.homologyPiece n → A.cycles (n : ℤ) :=
  Function.surjInv <|
    (ModuleCat.epi_iff_surjective (A.homologyπ (n : ℤ))).mp inferInstance

/-- The selected cycle projects to the homology class from which it was chosen. -/
@[simp] theorem homologyCycleRepresentative_spec
    (A : ChainDGAlgebra.{u, v} R) (n : ℕ) (x : A.homologyPiece n) :
    A.homologyπ n (A.homologyCycleRepresentative n x) = x := sorry

/-- A normalized selected cycle representing a class in canonical nonnegative homology. The
subtraction of the selected representative of zero makes the section preserve zero, which is
needed when applying it componentwise to an external direct sum. -/
noncomputable def selectedHomologyCycle (A : ChainDGAlgebra.{u, v} R) (n : ℕ)
    (x : A.homologyPiece n) : A.cycles (n : ℤ) :=
  A.homologyCycleRepresentative n x - A.homologyCycleRepresentative n 0

/-- The normalized selected homology cycle represents the class from which it was chosen. -/
@[simp] theorem selectedHomologyCycle_spec
    (A : ChainDGAlgebra.{u, v} R) (n : ℕ) (x : A.homologyPiece n) :
    A.homologyπ n (A.selectedHomologyCycle n x) = x := sorry

/-- The normalized selected cycle representing the zero homology class is zero. -/
@[simp] theorem selectedHomologyCycle_zero
    (A : ChainDGAlgebra.{u, v} R) (n : ℕ) :
    A.selectedHomologyCycle n 0 = 0 := sorry

/-- Take componentwise homology classes of a finite-support family of closed even chain values.
The output is assembled over the actual finite support of the input family. -/
noncomputable def homologyEvenClassOfCycles (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] (x : A.nonnegativePart.evenPart)
    (hx : ∀ d : ℕ, ((forget₂ (ModuleCat.{v} R) Ab).map
      (A.toChainComplex.sc (2 * d : ℤ)).g) (x d) = 0) :
    A.homologyNonnegativePart.evenPart :=
  @DFinsupp.sum ℕ A.homologyNonnegativePart.evenPart
    (fun d ↦ A.nonnegativePart.piece (2 * d)) (Classical.decEq ℕ) _
    (fun _ y ↦ Classical.propDecidable (y ≠ 0)) _ x fun d _ ↦
      A.homologyNonnegativePart.evenHom d <|
        A.homologyπ (2 * d) <|
          (A.toChainComplex.sc (2 * d : ℤ)).cyclesMk (x d) (hx d)

/-- Take componentwise homology classes of a finite-support family of closed positive-even chain
values, retaining the positive-even grading. -/
noncomputable def homologyEvenPositiveClassOfCycles (A : ChainDGAlgebra.{u, v} R)
    [A.IsStrictlyCommutative] (x : A.nonnegativePart.evenPositivePart)
    (hx : ∀ d : ℕ, ((forget₂ (ModuleCat.{v} R) Ab).map
      (A.toChainComplex.sc (2 * (d + 1) : ℤ)).g) (x d) = 0) :
    A.homologyNonnegativePart.evenPositivePart :=
  @DFinsupp.sum ℕ A.homologyNonnegativePart.evenPositivePart
    (fun d ↦ A.nonnegativePart.piece (2 * (d + 1))) (Classical.decEq ℕ) _
    (fun _ y ↦ Classical.propDecidable (y ≠ 0)) _ x fun d _ ↦
      A.homologyNonnegativePart.evenPositiveHom d <|
        A.homologyπ (2 * (d + 1)) <|
          (A.toChainComplex.sc (2 * (d + 1) : ℤ)).cyclesMk (x d) (hx d)

end ChainDGAlgebra
