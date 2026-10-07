module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Quotient
public import ReasLib.CategoryTheory.DerivedCategory.HomotopyLimit.Cohomology
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of ideal-power derived tensor systems

This leaf owns the cohomology observer on the canonical positive ideal-power derived tensor
system.  Its comparison theorems separate the explicit quotient-system limit from the equivalent
adic-completion presentation.
@stack 0EGS
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower

variable {A : Type u} [CommRing A]

/-- The cohomology inverse system of a fixed-right ideal-power derived tensor system. -/
@[stacks 0EGS "cohomology of the ideal-power derived tensor system"]
abbrev homologySystem
    (I : Ideal A) (K : DerivedCategory (ModuleCat A)) (i : ℤ) :
    SequentialInverseSystem (ModuleCat A) :=
  tensorSystem I K ⋙
    DerivedCategory.homologyFunctor (ModuleCat A) i

namespace HomologySystem

/-- Kollár-Kovács comparison in one degree, stated with the source-facing quotient-system limit.
Only the preceding cohomology system needs the Mittag-Leffler hypothesis. -/
@[stacks 0EGS "Kollár-Kovács quotient-system limit comparison"]
theorem quotientLimit [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat A)) (i : ℤ)
    (hKfinite : ∀ j : ℤ,
      Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat A) j).obj K))
    (hML : (homologySystem I K (i - 1)).IsMittagLeffler) :
    IsIsomorphic
      (limit (Ideal.PowerQuotient.positiveSystem I
        ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K)))
      (limit (homologySystem I K i)) := sorry

/-- Adic-completion presentation of the Kollár-Kovács comparison in one degree. -/
@[stacks 0EGS "Kollár-Kovács adic-completion limit comparison"]
theorem adicLimit [IsNoetherianRing A]
    (I : Ideal A) (K : DerivedCategory (ModuleCat A)) (i : ℤ)
    (hKfinite : ∀ j : ℤ,
      Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat A) j).obj K))
    (hML : (homologySystem I K (i - 1)).IsMittagLeffler) :
    IsIsomorphic
      (ModuleCat.of A
        (AdicCompletion I
          ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K)))
      (limit (homologySystem I K i)) := sorry

end HomologySystem

end CategoryTheory.DerivedCategory.IdealPower
