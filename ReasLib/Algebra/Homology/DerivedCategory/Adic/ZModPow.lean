module

public import Mathlib.Data.ZMod.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension

/-!
# Derived scalar extension between consecutive prime-power residue rings
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.DerivedCategory.IsPerfect

/-- The canonical reduction `ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (n + 1))`. -/
abbrev zmodPowStepHom (ℓ n : ℕ) : ZMod (ℓ ^ (n + 2)) →+* ZMod (ℓ ^ (n + 1)) :=
  ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) _

/-- Derived extension of scalars along `zmodPowStepHom`, i.e. `- ⊗^L_{ZMod (ℓ^{n+2})} ZMod (ℓ^{n+1})`. -/
noncomputable abbrev derivedBaseChange (ℓ n : ℕ) :
    DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 2)))) ⥤
      DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))) :=
  ModuleCat.derivedExtensionOfScalars (zmodPowStepHom ℓ n)

end CategoryTheory.DerivedCategory.IsPerfect
