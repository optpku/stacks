/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Kernel
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization

@[expose] public section

/-!
# Kernels and Morphisms Inverted by Verdier Quotients

These statements convert objectwise vanishing conditions into the morphism
property required by `Localization.lift`.  They are kept separate from the
quotient construction so the latter remains a data-and-instance leaf.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.ObjectProperty

open Limits MorphismProperty Pretriangulated

namespace VerdierQuotient

section Homological

variable {D : Type u₁} {A : Type u₂}
  [Category.{v₁} D] [Category.{v₂} A]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [Abelian A]

/-- Stacks 05RJ: if a homological functor vanishes on `P`, it inverts the
cone-defined Verdier system `P.trW`. -/
@[stacks 05RJ]
theorem trW_isInvertedBy_of_le_homologicalKernel
    (P : ObjectProperty D) (H : D ⥤ A) [H.IsHomological]
    (hP : P ≤ H.homologicalKernel) :
    P.trW.IsInvertedBy H := sorry

end Homological

section Triangulated

variable {D : Type u₁} {E : Type u₃}
  [Category.{v₁} D] [Category.{v₃} E]
  [HasZeroObject D] [HasZeroObject E]
  [HasShift D ℤ] [HasShift E ℤ]
  [Preadditive D] [Preadditive E]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated D] [Pretriangulated E]

/-- Stacks 05RJ: if an exact functor vanishes on `P`, it inverts the
cone-defined Verdier system `P.trW`. -/
@[stacks 05RJ]
theorem trW_isInvertedBy_of_le_kernel
    (P : ObjectProperty D) (F : D ⥤ E) [F.CommShift ℤ] [F.IsTriangulated]
    (hP : P ≤ F.kernel) :
    P.trW.IsInvertedBy F := sorry

end Triangulated

section Kernel

variable {D : Type u₁} [Category.{v₁} D]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D]
  (P : ObjectProperty D) [P.IsTriangulated]

/-- Stacks 05RK: the kernel of the Verdier quotient functor is the retract
closure of the object property being quotiented. -/
@[stacks 05RK]
theorem kernel_eq_retractClosure :
    Functor.kernel (verdierQuotientFunctor P) = P.retractClosure := sorry

/-- Stacks 05RL: a retract-stable triangulated object property is recovered as the kernel of
its Verdier quotient functor. -/
@[stacks 05RL]
theorem kernel_eq_self [P.IsStableUnderRetracts] :
    Functor.kernel (verdierQuotientFunctor P) = P := sorry

/-- An object belongs to the kernel of the Verdier quotient functor exactly
when it is a retract of an object satisfying `P`. -/
@[stacks 05RK]
theorem mem_kernel_iff (X : D) :
    Functor.kernel (verdierQuotientFunctor P) X ↔
      ∃ Y : D, P Y ∧ Nonempty (Retract X Y) := sorry

/-- Biproduct presentation of `mem_kernel_iff`. -/
@[stacks 05RK]
theorem mem_kernel_iff_biprod (X : D) :
    Functor.kernel (verdierQuotientFunctor P) X ↔
      ∃ (X' Y : D), P Y ∧ Nonempty (X ⊞ X' ≅ Y) := sorry

/-- The kernel of the Verdier quotient is initial among retract-stable object
properties containing `P`. -/
@[stacks 05RK]
theorem kernel_le_iff (R : ObjectProperty D) [R.IsStableUnderRetracts] :
    Functor.kernel (verdierQuotientFunctor P) ≤ R ↔ P ≤ R := sorry

/-- The kernel of any localization model for `P.trW` is `P` when `P` is stable under retracts.
This formulation lets downstream developments use their chosen quotient category directly. -/
@[stacks 05RT "kernel of a chosen Verdier localization model"]
theorem kernel_eq_self_of_isLocalization
    {E : Type u₃} [Category.{v₃} E] [P.IsStableUnderRetracts]
    (L : D ⥤ E) [L.IsLocalization P.trW] :
    Functor.kernel L = P := sorry

/-- Objectwise form of `kernel_eq_self_of_isLocalization`. -/
@[stacks 05RT "kernel membership in a chosen Verdier localization model"]
theorem mem_kernel_iff_of_isLocalization
    {E : Type u₃} [Category.{v₃} E] [P.IsStableUnderRetracts]
    (L : D ⥤ E) [L.IsLocalization P.trW] (X : D) :
    Functor.kernel L X ↔ P X := sorry

end Kernel


end VerdierQuotient

end CategoryTheory.ObjectProperty
