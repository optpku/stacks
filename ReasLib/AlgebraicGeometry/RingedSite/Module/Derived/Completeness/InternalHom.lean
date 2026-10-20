module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completeness
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InternalHom

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

/-- The derived internal Hom into an `I`-derived-complete object is `I`-derived complete. -/
theorem internalHom_isDerivedComplete (I : Subobject (unitModule J O))
    (K L : RingedSiteDerived.{u, u, u, u} J O)
    (hL : IsDerivedCompleteWithRespectTo.{u, u, u, u} L I) :
    IsDerivedCompleteWithRespectTo.{u, u, u, u}
      (InternalHom.obj K L) I := sorry

end RingedSite.Hom.ModuleDerived
