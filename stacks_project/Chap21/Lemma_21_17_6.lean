module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Homology.HomotopyCategory.KFlat.Triangulated
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

/- Lemma 21.17.6 (1): in the homotopy category of modules on a ringed site, K-flatness of the
first two objects of a distinguished triangle implies K-flatness of the third. -/
@[stacks 07A3 "(1)"] #check
  (HomotopyCategory.IsKFlat.obj₃_of_distinguished :
    (T : Triangle (HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ))) →
      T ∈ distTriang (HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ)) →
      T.obj₁.IsKFlat → T.obj₂.IsKFlat → T.obj₃.IsKFlat)

/- Lemma 21.17.6 (2): in the homotopy category of modules on a ringed site, K-flatness of the
first and third objects of a distinguished triangle implies K-flatness of the second. -/
@[stacks 07A3 "(2)"] #check
  (HomotopyCategory.IsKFlat.obj₂_of_distinguished :
    (T : Triangle (HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ))) →
      T ∈ distTriang (HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ)) →
      T.obj₁.IsKFlat → T.obj₃.IsKFlat → T.obj₂.IsKFlat)

/- Lemma 21.17.6 (3): in the homotopy category of modules on a ringed site, K-flatness of the
last two objects of a distinguished triangle implies K-flatness of the first. -/
@[stacks 07A3 "(3)"] #check
  (HomotopyCategory.IsKFlat.obj₁_of_distinguished :
    (T : Triangle (HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ))) →
      T ∈ distTriang (HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ)) →
      T.obj₂.IsKFlat → T.obj₃.IsKFlat → T.obj₁.IsKFlat)

end SheafOfModules.RingedSite
