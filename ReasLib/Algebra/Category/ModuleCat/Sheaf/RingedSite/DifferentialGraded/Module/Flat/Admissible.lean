module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Admissible
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat
public import ReasLib.Algebra.Homology.CochainComplex.Bimod.Flat.Admissible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness and admissible short exact sequences of DG modules

The generic two-out-of-three API for modules over monoid objects specializes to differential
graded module sheaves.  Each of graded flatness, relative K-flatness, and their conjunction is
exposed separately so downstream code can assume only the property it uses.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}} {A : DGA(O)}

namespace IsGradedFlat

/-- Graded flatness passes to the quotient in an admissible short exact sequence of DG modules. -/
@[stacks 0FSC "graded-flat admissible quotient"]
theorem of_left_middle (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₁ : IsGradedFlat S.X₁) (h₂ : IsGradedFlat S.X₂) : IsGradedFlat S.X₃ := sorry

/-- Graded flatness is closed under admissible extensions of DG modules. -/
@[stacks 0FSC "graded-flat admissible extension"]
theorem of_left_right (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₁ : IsGradedFlat S.X₁) (h₃ : IsGradedFlat S.X₃) : IsGradedFlat S.X₂ := sorry

/-- Graded flatness passes to the kernel in an admissible short exact sequence of DG modules. -/
@[stacks 0FSC "graded-flat admissible kernel"]
theorem of_middle_right (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₂ : IsGradedFlat S.X₂) (h₃ : IsGradedFlat S.X₃) : IsGradedFlat S.X₁ := sorry

end IsGradedFlat

namespace IsKFlat

/-- Relative K-flatness passes to the quotient in an admissible short exact sequence of DG
modules. -/
@[stacks 0FSC "K-flat admissible quotient"]
theorem of_left_middle (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₁ : IsKFlat S.X₁) (h₂ : IsKFlat S.X₂) : IsKFlat S.X₃ := sorry

/-- Relative K-flatness is closed under admissible extensions of DG modules. -/
@[stacks 0FSC "K-flat admissible extension"]
theorem of_left_right (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₁ : IsKFlat S.X₁) (h₃ : IsKFlat S.X₃) : IsKFlat S.X₂ := sorry

/-- Relative K-flatness passes to the kernel in an admissible short exact sequence of DG
modules. -/
@[stacks 0FSC "K-flat admissible kernel"]
theorem of_middle_right (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₂ : IsKFlat S.X₂) (h₃ : IsKFlat S.X₃) : IsKFlat S.X₁ := sorry

end IsKFlat

namespace IsGoodAtBase

/-- Fixed-base goodness passes to the quotient in an admissible short exact sequence of DG
modules. -/
@[stacks 0FSC "fixed-base good admissible quotient"]
theorem of_left_middle (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₁ : IsGoodAtBase S.X₁) (h₂ : IsGoodAtBase S.X₂) : IsGoodAtBase S.X₃ := sorry

/-- Fixed-base goodness is closed under admissible extensions of DG modules. -/
@[stacks 0FSC "fixed-base good admissible extension"]
theorem of_left_right (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₁ : IsGoodAtBase S.X₁) (h₃ : IsGoodAtBase S.X₃) : IsGoodAtBase S.X₂ := sorry

/-- Fixed-base goodness passes to the kernel in an admissible short exact sequence of DG modules. -/
@[stacks 0FSC "fixed-base good admissible kernel"]
theorem of_middle_right (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₂ : IsGoodAtBase S.X₂) (h₃ : IsGoodAtBase S.X₃) : IsGoodAtBase S.X₁ := sorry

end IsGoodAtBase

end SheafOfModules.RingedSite.DifferentialGradedModule

end
