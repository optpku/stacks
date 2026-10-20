/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.FunctorialResolution
public import ReasLib.CategoryTheory.DerivedCategory.SmallHom

@[expose] public section

/-!
# Small Hom Types for Grothendieck Derived Categories

K-injective replacements make the localization of the homotopy category locally small.  The
core statement only asks for replacements; the Grothendieck specialization obtains them from the
reusable functorial-resolution owner.
-/

open CategoryTheory.Localization
open ComplexShape

universe w v u

namespace CategoryTheory.DerivedCategory.HomotopyLocalizedHom

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- K-injective replacements of all cochain complexes make every localized Hom type in the
homotopy category `w`-small. -/
theorem of_replacements [LocallySmall.{w} A]
    (replacement : ∀ L : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (_ : I.IsKInjective) (f : L ⟶ I), QuasiIso f)
    (K L : HomotopyCategory A (up ℤ)) :
    HasSmallLocalizedHom.{w} (HomotopyCategory.quasiIso A (up ℤ)) K L := sorry

/-- A functorial K-injective resolution supplies small localized Hom types in the homotopy
category. -/
theorem of_functorialResolution [LocallySmall.{w} A]
    (R : CochainComplex.KInjectiveResolution.Functorial A)
    (K L : HomotopyCategory A (up ℤ)) :
    HasSmallLocalizedHom.{w} (HomotopyCategory.quasiIso A (up ℤ)) K L := sorry

/-- Remark 19.13.3: the derived localization of a Grothendieck abelian category has small Hom
types. -/
@[stacks 079Q]
theorem of_grothendieck [IsGrothendieckAbelian.{w} A]
    (K L : HomotopyCategory A (up ℤ)) :
    HasSmallLocalizedHom.{w} (HomotopyCategory.quasiIso A (up ℤ)) K L := sorry

end CategoryTheory.DerivedCategory.HomotopyLocalizedHom
