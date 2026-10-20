module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completeness.InternalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/- Lemma 52.6.5: if `L` is derived complete with respect to the ideal sheaf `I`, then
`RHom_O(K, L)` is derived complete with respect to `I` for every `K ∈ D(O)`. -/
@[stacks 099A] #check (RingedSite.Hom.ModuleDerived.internalHom_isDerivedComplete :
  ∀ (I : Subobject (unitModule J O))
    (K L : RingedSiteDerived.{u, u, u, u} J O),
    IsDerivedCompleteWithRespectTo.{u, u, u, u} L I →
      IsDerivedCompleteWithRespectTo.{u, u, u, u}
        (RingedSite.Hom.ModuleDerived.InternalHom.obj K L) I)

end RingedSite.Hom.ModuleDerived
