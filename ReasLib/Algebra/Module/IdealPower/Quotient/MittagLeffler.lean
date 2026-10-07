module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Epi
import Mathlib.Tactic.CrossRefAttribute

/-!
# Mittag-Leffler ideal-power quotient systems

The positive ideal-power quotient system has epimorphic transition maps, hence is
Mittag-Leffler.  Keeping this fact next to the canonical `Ideal.PowerQuotient` owner avoids
reproving it for every principal or cohomological specialization.
@stack 0EGS
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace Ideal.PowerQuotient

variable {R : Type u} [CommRing R]

/-- Every successor transition in a positive ideal-power quotient system is epimorphic. -/
noncomputable instance positiveStep_epi
    (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    Epi (positiveStep I M n) := sorry

/-- The positive ideal-power quotient system of a module is Mittag-Leffler. -/
@[stacks 0EGS "Mittag-Leffler ideal-power quotient system"]
theorem positiveSystem_isMittagLeffler
    (I : Ideal R) (M : ModuleCat.{v} R) :
    (positiveSystem I M).IsMittagLeffler := sorry

end Ideal.PowerQuotient
