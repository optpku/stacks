module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion

/-!
# Constant sheaves of integers modulo a natural number

The constant additive sheaf with coefficients in `ULift (ZMod n)` is obtained by
sheafifying the constant presheaf, with the coefficient universe independent of the site.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- The constant additive sheaf of integers modulo `n` on a site. -/
noncomputable abbrev constantZModSheaf (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{w}] (n : ℕ) : Sheaf J AddCommGrpCat.{w} :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} (ZMod n)))

/-- The constant additive sheaf of integers modulo `n` is the sheafification of
the constant presheaf with coefficients in `ULift (ZMod n)`. -/
theorem constantZModSheaf_eq_sheafification (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{w}] (n : ℕ) :
    constantZModSheaf J n = (presheafToSheaf J AddCommGrpCat.{w}).obj
      ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{w} (ZMod n)))) := sorry

/-- The constant additive sheaf of integers modulo a nonzero natural number is
locally torsion. -/
theorem constantZModSheaf_isLocallyTorsion (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}] (n : ℕ) (hn : n ≠ 0) :
    Sheaf.IsLocallyTorsion (constantZModSheaf J n) := sorry

end CategoryTheory
