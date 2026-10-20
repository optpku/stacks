module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.IdealPower

/-!
# Ideal-power quotients of module sheaves

The reusable construction is owned by `ReasLib.Algebra.Category.ModuleCat.Sheaf.IdealPower`.
-/

@[expose] public section

open CategoryTheory

universe u v w

/- The sheafified exact-power quotient construction. -/
#check
  (CategoryTheory.Sheaf.IdealPower.quotient :
    {C : Type u} → [Category.{v} C] → {R : Type w} → [CommRing R] →
      {J : GrothendieckTopology C} → [HasWeakSheafify J (ModuleCat.{w} R)] →
      Ideal R → Sheaf J (ModuleCat.{w} R) → ℕ → Sheaf J (ModuleCat.{w} R))
