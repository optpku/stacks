/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Category
public import ReasLib.RingTheory.Ideal.Principal

/-!
# Colimits of derived-complete modules over the p-adic integers
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.DerivedComplete

/-- For a prime `p`, the principal ideal `(p)` is finitely generated, but the inclusion of
derived-complete `ℤ_[p]`-modules does not preserve all colimits. -/
theorem padic_inclusion_not_preservesColimits (p : ℕ) [Fact p.Prime] :
    (principalIdeal (p : ℤ_[p])).FG ∧
      ¬ PreservesColimits (inclusion (principalIdeal (p : ℤ_[p]))) := sorry

/-- For a prime `p`, the inclusion of derived-complete `ℤ_[p]`-modules does not preserve
countable coproducts, despite `(p)` being finitely generated. -/
theorem padic_inclusion_not_preservesCoproducts (p : ℕ) [Fact p.Prime] :
    (principalIdeal (p : ℤ_[p])).FG ∧
      ¬ PreservesColimitsOfShape (Discrete ℕ)
        (inclusion (principalIdeal (p : ℤ_[p]))) := sorry

/-- For a prime `p`, sequential filtered colimits of derived-complete `ℤ_[p]`-modules
are not exact, even though `(p)` is finitely generated. -/
theorem padic_not_hasExactColimitsOfShape_nat (p : ℕ) [Fact p.Prime] :
    (principalIdeal (p : ℤ_[p])).FG ∧
      ∀ [HasColimitsOfShape ℕ (category (principalIdeal (p : ℤ_[p])))],
        ¬ Nonempty (HasExactColimitsOfShape ℕ
          (category (principalIdeal (p : ℤ_[p])))) := sorry

/-- For a prime `p`, the category of derived-complete `ℤ_[p]`-modules with respect to `(p)`
is not Grothendieck abelian, although `(p)` is finitely generated. -/
theorem padic_not_isGrothendieckAbelian (p : ℕ) [Fact p.Prime] :
    (principalIdeal (p : ℤ_[p])).FG ∧
      ¬ IsGrothendieckAbelian (category (principalIdeal (p : ℤ_[p]))) := sorry

end ModuleCat.DerivedComplete
