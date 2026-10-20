module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Koszul.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Koszul
import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication in Koszul complexes on ringed sites

The fixed-degree Leibniz rule for the objectwise Koszul differential descends through monoidal
module sheafification.  This leaf deliberately stops at the compatibility morphism and does not
introduce a second differential graded algebra owner.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Koszul

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The sheafified Koszul differential satisfies the graded Leibniz rule for exterior
multiplication in two positive degrees. -/
@[stacks 062K "ringed-site graded Leibniz rule"]
theorem differential_mul
    {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) (n m : ℕ) :
    ExteriorPower.mul O F (n + 1) (m + 1) ≫
        eqToHom
          (congrArg (ExteriorPower.sheaf O F)
            (Nat.succ_add n (m + 1))) ≫
        differential O phi (n + (m + 1)) =
      (differential O phi n ▷ ExteriorPower.sheaf O F (m + 1)) ≫
          ExteriorPower.mul O F n (m + 1) +
        ((-1 : ℤ) ^ (n + 1)) •
          ((ExteriorPower.sheaf O F (n + 1) ◁ differential O phi m) ≫
            ExteriorPower.mul O F (n + 1) m ≫
            eqToHom
              (congrArg (ExteriorPower.sheaf O F)
                ((Nat.succ_add n m).trans (Nat.add_succ n m).symm))) := sorry

/-- The sheafified Koszul differential commutes with exterior multiplication by a degree-zero
element on the right. -/
@[stacks 062K "ringed-site right degree-zero Leibniz rule"]
theorem differential_mul_zero_right
    {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) (n : ℕ) :
    ExteriorPower.mul O F (n + 1) 0 ≫
        eqToHom
          (congrArg (ExteriorPower.sheaf O F) (Nat.add_zero (n + 1))) ≫
        differential O phi n =
      (differential O phi n ▷ ExteriorPower.sheaf O F 0) ≫
        ExteriorPower.mul O F n 0 ≫
        eqToHom
          (congrArg (ExteriorPower.sheaf O F) (Nat.add_zero n)) := sorry

/-- The sheafified Koszul differential commutes with exterior multiplication by a degree-zero
element on the left. -/
@[stacks 062K "ringed-site left degree-zero Leibniz rule"]
theorem differential_zero_mul
    {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) (m : ℕ) :
    ExteriorPower.mul O F 0 (m + 1) ≫
        eqToHom
          (congrArg (ExteriorPower.sheaf O F) (Nat.zero_add (m + 1))) ≫
        differential O phi m =
      (ExteriorPower.sheaf O F 0 ◁ differential O phi m) ≫
        ExteriorPower.mul O F 0 m ≫
        eqToHom
          (congrArg (ExteriorPower.sheaf O F) (Nat.zero_add m)) := sorry

end SheafOfModules.RingedSite.Koszul
