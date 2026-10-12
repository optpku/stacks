/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion.Kernel
public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel realization of quotient presentations

This leaf contains only the characterization bridge that needs the exact sequential-colimit
infrastructure.  The quotient presentation and its stagewise row API remain available from the
narrower `PrincipalTorsion.Quotient` owner. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SequentialInverseSystem.PrincipalTorsion

section Abelian

variable {R : Type w} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- Lemma 20.36.1 (0H39), `(4) → (3)`: exact sequential colimits turn a torsion-free quotient
presentation into a divisible power-kernel presentation. -/
@[stacks 0H39 "quotient presentation gives divisible kernel presentation"]
theorem isKernelPresented_of_isQuotientPresented
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    (r : R) (F : SequentialInverseSystem C) :
    IsQuotientPresented r F → IsKernelPresented r F := sorry

end Abelian

end CategoryTheory.SequentialInverseSystem.PrincipalTorsion
