module

public import stacks_project.Chap91.Remark_91_10_7_Extension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening

open CategoryTheory

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O' O : Sheaf J CommRingCat.{max u v}}

#check (SheafOfModules.RingedSite.FirstOrderThickening.Hom.id :
  (π : O' ⟶ O) → [SheafOfModules.RingedSite.IsFirstOrderThickening π] →
    SheafOfModules.RingedSite.FirstOrderThickening.Hom π π)

end
