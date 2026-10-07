module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completeness

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules.RingedSite
open IdealSheaf

noncomputable section

universe u v w z

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, z}]

/- Definition 52.6.4: a derived `O`-module `K` is derived complete with respect to the ideal
sheaf `I` when, for every object `U` and every `f ∈ I(U)`, a homotopy-limit representative
`T(K|_U, f)` of the localization-away tower exists and is zero in `D(O_U)`. -/
@[stacks 0999]
#check (RingedSite.Hom.ModuleDerived.IsDerivedCompleteWithRespectTo :
    ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O) →
      Subobject (unitModule J O) → Prop)

end RingedSite.Hom.ModuleDerived
