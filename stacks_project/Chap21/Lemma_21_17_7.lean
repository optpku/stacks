module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.ShortExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

/- Lemma 21.17.7 (1): in a short exact sequence of complexes of modules on a ringed site, if the
cokernel complex is termwise flat and the first two complexes are K-flat, then the third is
K-flat. -/
@[stacks 0G7B "(1)"] #check
  (CochainComplex.IsKFlat.obj₃_of_shortExact :
    {S : ShortComplex (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)} →
      S.ShortExact → HomologicalComplex.IsTermwiseFlat S.X₃ →
      S.X₁.IsKFlat → S.X₂.IsKFlat → S.X₃.IsKFlat)

/- Lemma 21.17.7 (2): in a short exact sequence of complexes of modules on a ringed site, if the
cokernel complex is termwise flat and the outer complexes are K-flat, then the middle one is
K-flat. -/
@[stacks 0G7B "(2)"] #check
  (CochainComplex.IsKFlat.obj₂_of_shortExact :
    {S : ShortComplex (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)} →
      S.ShortExact → HomologicalComplex.IsTermwiseFlat S.X₃ →
      S.X₁.IsKFlat → S.X₃.IsKFlat → S.X₂.IsKFlat)

/- Lemma 21.17.7 (3): in a short exact sequence of complexes of modules on a ringed site, if the
cokernel complex is termwise flat and the last two complexes are K-flat, then the first is
K-flat. -/
@[stacks 0G7B "(3)"] #check
  (CochainComplex.IsKFlat.obj₁_of_shortExact :
    {S : ShortComplex (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)} →
      S.ShortExact → HomologicalComplex.IsTermwiseFlat S.X₃ →
      S.X₂.IsKFlat → S.X₃.IsKFlat → S.X₁.IsKFlat)

end SheafOfModules.RingedSite
