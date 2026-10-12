/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Generating-Family Approximations

@stack 09SN

This leaf owns the object-property and triangle data underlying sequential
approximations by arbitrary coproducts of shifts of a family.  It is independent
of compactness and of any chosen homotopy-colimit construction.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe w v u

namespace CategoryTheory

namespace ObjectProperty

section

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]
  [HasCoproducts.{max u v w} D]
variable {I : Type w} (E : I → D)

/-- Objects isomorphic to arbitrary coproducts of shifts of members of `E`. -/
@[stacks 09SN]
def directSumOfShifts : ObjectProperty D := fun A ↦
  ∃ (J : Type (max u v w)) (ι : J → I) (shift : J → ℤ),
    Nonempty ((∐ fun j : J ↦ E (ι j)⟦shift j⟧) ≅ A)

/-- Arbitrary direct sums of shifts of a family are stable under isomorphism. -/
@[stacks 09SN]
instance directSumOfShifts_isClosedUnderIsomorphisms :
    (directSumOfShifts E).IsClosedUnderIsomorphisms := sorry

end

end ObjectProperty

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasCoproducts.{max u v w} D]
variable {I : Type w} (E : I → D)

/-- A sequential approximation whose initial object and successive triangle pieces are direct
sums of shifts of a generating family. -/
@[stacks 09SN]
def IsGeneratingFamilyApproximation
    (X : ℕ → D) (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    (Y : ℕ → D) (triangleHom : ∀ n : ℕ, Y n ⟶ X n)
    (triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧) : Prop :=
  ObjectProperty.directSumOfShifts E (X 0) ∧
    (∀ n : ℕ, ObjectProperty.directSumOfShifts E (Y n)) ∧
    (∀ n : ℕ, Triangle.mk (triangleHom n) (map n) (triangleConnecting n) ∈ distTriang D)

namespace IsGeneratingFamilyApproximation

variable {E : I → D}

/-- The initial object of a generating-family approximation is a direct sum of shifts. -/
@[stacks 09SN]
theorem initial {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (h : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) :
    ObjectProperty.directSumOfShifts E (X 0) := sorry

/-- Every triangle piece of a generating-family approximation is a direct sum of shifts. -/
@[stacks 09SN]
theorem pieces {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (h : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) (n : ℕ) :
    ObjectProperty.directSumOfShifts E (Y n) := sorry

/-- The triangle at every stage of a generating-family approximation is distinguished. -/
@[stacks 09SN]
theorem triangleDistinguished {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (h : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) (n : ℕ) :
    Triangle.mk (triangleHom n) (map n) (triangleConnecting n) ∈ distTriang D := sorry

end IsGeneratingFamilyApproximation

end

end CategoryTheory
