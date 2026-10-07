module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.BoundedAbove
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section


variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/- Lemma 21.17.8: a bounded-above cochain complex of flat modules on a ringed site is K-flat. -/
@[stacks 06YQ]
#check
  (CochainComplex.IsTermwiseFlat.isKFlat_of_boundedAbove :
    {K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ} →
      HomologicalComplex.IsTermwiseFlat K →
      CochainComplex.minus (ringedSiteModuleCategory J 𝒪) K → K.IsKFlat)

end


end SheafOfModules.RingedSite
