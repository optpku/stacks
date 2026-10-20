module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion.Power
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel presentations of principal torsion systems

A kernel presentation identifies the tail of a sequential inverse system with the positive
power-kernel system of an object on which the chosen scalar acts epimorphically.  It is the
categorical owner of the divisible-kernel condition, independent of sheaves or global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.SequentialInverseSystem.PrincipalTorsion

variable {R : Type w} [CommSemiring R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C] [HasKernels C]

/-- A chosen realization of the tail of `F` as the principal-power kernel system of a divisible
object. -/
@[stacks 0H39 "divisible principal-power kernel presentation"]
structure KernelPresentation (r : R) (F : SequentialInverseSystem C) where
  /-- The ambient object whose power kernels realize the tower. -/
  object : C
  /-- Multiplication by `r` on the ambient object is epimorphic. -/
  divisible : CategoryTheory.Linear.PrincipalPower.IsDivisible r object
  /-- The shifted system is the canonical principal-power kernel system. -/
  shiftIso : F.shift 1 ≅ CategoryTheory.Linear.PrincipalPower.kernelSystem r object

/-- A divisible object and an isomorphism of its power-kernel system with the positive tail
determine a kernel presentation. -/
def KernelPresentation.ofIso {r : R} {F : SequentialInverseSystem C}
    (object : C) (h_divisible : CategoryTheory.Linear.PrincipalPower.IsDivisible r object)
    (shiftIso : F.shift 1 ≅ CategoryTheory.Linear.PrincipalPower.kernelSystem r object) :
    KernelPresentation r F :=
  { object := object
    divisible := h_divisible
    shiftIso := shiftIso }

/-- A sequential inverse system is realized by power kernels of a divisible object. -/
@[stacks 0H39 "existence of a divisible power-kernel presentation"]
def IsKernelPresented (r : R) (F : SequentialInverseSystem C) : Prop :=
  Nonempty (KernelPresentation r F)

/-- A kernel presentation exists exactly when the positive tail is isomorphic to the
power-kernel system of a divisible object. -/
theorem isKernelPresented_iff (r : R) (F : SequentialInverseSystem C) :
    IsKernelPresented r F ↔
      ∃ G : C, CategoryTheory.Linear.PrincipalPower.IsDivisible r G ∧
        Nonempty (F.shift 1 ≅ CategoryTheory.Linear.PrincipalPower.kernelSystem r G) := sorry

section Abelian

variable {R : Type w} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- A divisible power-kernel presentation induces a principal-power presentation. -/
theorem isPowerPresented_of_isKernelPresented
    (r : R) (F : SequentialInverseSystem C) :
    IsKernelPresented r F → IsPowerPresented r F := sorry

/-- Exact sequential colimits turn a principal torsion presentation into a divisible
principal-power kernel presentation. -/
@[stacks 0H39 "principal torsion presentation gives kernel presentation"]
theorem isKernelPresented_of_isPresented
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    (r : R) (F : SequentialInverseSystem C) :
    IsPresented r F → IsKernelPresented r F := sorry

/-- Exact sequential colimits construct a divisible power-kernel presentation from a
principal-power presentation. -/
theorem isKernelPresented_of_isPowerPresented
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    (r : R) (F : SequentialInverseSystem C) :
    IsPowerPresented r F → IsKernelPresented r F := sorry

/-- In an abelian category with exact sequential colimits, divisible power-kernel and
principal-power presentations are equivalent. -/
@[stacks 0H39 "kernel and power presentations are equivalent"]
theorem isKernelPresented_iff_isPowerPresented
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    (r : R) (F : SequentialInverseSystem C) :
    IsKernelPresented r F ↔ IsPowerPresented r F := sorry

/-- In an abelian category with exact sequential colimits, kernel and principal-torsion
presentations are equivalent. -/
@[stacks 0H39 "kernel and principal torsion presentations are equivalent"]
theorem isKernelPresented_iff_isPresented
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    (r : R) (F : SequentialInverseSystem C) :
    IsKernelPresented r F ↔ IsPresented r F := sorry

end Abelian

end CategoryTheory.SequentialInverseSystem.PrincipalTorsion
