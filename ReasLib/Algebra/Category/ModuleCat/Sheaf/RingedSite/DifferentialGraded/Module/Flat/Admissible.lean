/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
variable {O : Sheaf J CommRingCat.{max u v w}} {A : DGA(O)}

namespace IsGradedFlat

/-- Graded flatness passes to the quotient in an admissible short exact sequence of DG modules. -/
@[stacks 0FSC "graded-flat admissible quotient"]
theorem of_left_middle (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₁ : IsGradedFlat.{u, v, max u v w} S.X₁)
    (h₂ : IsGradedFlat.{u, v, max u v w} S.X₂) :
    IsGradedFlat.{u, v, max u v w} S.X₃ := sorry

/-- Graded flatness is closed under admissible extensions of DG modules. -/
@[stacks 0FSC "graded-flat admissible extension"]
theorem of_left_right (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₁ : IsGradedFlat.{u, v, max u v w} S.X₁)
    (h₃ : IsGradedFlat.{u, v, max u v w} S.X₃) :
    IsGradedFlat.{u, v, max u v w} S.X₂ := sorry

/-- Graded flatness passes to the kernel in an admissible short exact sequence of DG modules. -/
@[stacks 0FSC "graded-flat admissible kernel"]
theorem of_middle_right (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₂ : IsGradedFlat.{u, v, max u v w} S.X₂)
    (h₃ : IsGradedFlat.{u, v, max u v w} S.X₃) :
    IsGradedFlat.{u, v, max u v w} S.X₁ := sorry

end IsGradedFlat

namespace IsKFlat

/-- Relative K-flatness passes to the quotient in an admissible short exact sequence of DG
modules. -/
@[stacks 0FSC "K-flat admissible quotient"]
theorem of_left_middle (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₁ : IsKFlat.{u, v, max u v w} S.X₁)
    (h₂ : IsKFlat.{u, v, max u v w} S.X₂) :
    IsKFlat.{u, v, max u v w} S.X₃ := sorry

/-- Relative K-flatness is closed under admissible extensions of DG modules. -/
@[stacks 0FSC "K-flat admissible extension"]
theorem of_left_right (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₁ : IsKFlat.{u, v, max u v w} S.X₁)
    (h₃ : IsKFlat.{u, v, max u v w} S.X₃) :
    IsKFlat.{u, v, max u v w} S.X₂ := sorry

/-- Relative K-flatness passes to the kernel in an admissible short exact sequence of DG
modules. -/
@[stacks 0FSC "K-flat admissible kernel"]
theorem of_middle_right (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₂ : IsKFlat.{u, v, max u v w} S.X₂)
    (h₃ : IsKFlat.{u, v, max u v w} S.X₃) :
    IsKFlat.{u, v, max u v w} S.X₁ := sorry

end IsKFlat

namespace IsGoodAtBase

/-- Fixed-base goodness passes to the quotient in an admissible short exact sequence of DG
modules. -/
@[stacks 0FSC "fixed-base good admissible quotient"]
theorem of_left_middle (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₁ : IsGoodAtBase.{u, v, max u v w} S.X₁)
    (h₂ : IsGoodAtBase.{u, v, max u v w} S.X₂) :
    IsGoodAtBase.{u, v, max u v w} S.X₃ := sorry

/-- Fixed-base goodness is closed under admissible extensions of DG modules. -/
@[stacks 0FSC "fixed-base good admissible extension"]
theorem of_left_right (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₁ : IsGoodAtBase.{u, v, max u v w} S.X₁)
    (h₃ : IsGoodAtBase.{u, v, max u v w} S.X₃) :
    IsGoodAtBase.{u, v, max u v w} S.X₂ := sorry

/-- Fixed-base goodness passes to the kernel in an admissible short exact sequence of DG modules. -/
@[stacks 0FSC "fixed-base good admissible kernel"]
theorem of_middle_right (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)
    (h₂ : IsGoodAtBase.{u, v, max u v w} S.X₂)
    (h₃ : IsGoodAtBase.{u, v, max u v w} S.X₃) :
    IsGoodAtBase.{u, v, max u v w} S.X₁ := sorry

end IsGoodAtBase

end SheafOfModules.RingedSite.DifferentialGradedModule

end
