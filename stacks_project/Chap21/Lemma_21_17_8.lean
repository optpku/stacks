/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.BoundedAbove
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
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
  (HomologicalComplex.IsTermwiseFlat.isKFlat_of_boundedAbove :
    {K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ} →
      HomologicalComplex.IsTermwiseFlat K →
      CochainComplex.minus (ringedSiteModuleCategory J 𝒪) K → K.IsKFlat)

end


end SheafOfModules.RingedSite
