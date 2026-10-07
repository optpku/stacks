module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TrivSqZeroExt

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.TrivSqZeroExt

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

#check (sectionRing :
  (R : Sheaf J CommRingCat.{w}) →
    SheafOfModules.{w} (ringSheaf J R) → Cᵒᵖ → CommRingCat.{w})

#check (trivSqZeroExt :
  (R : Sheaf J CommRingCat.{w}) →
    SheafOfModules.{w} (ringSheaf J R) → Sheaf J CommRingCat.{w})

#check (fst :
  (R : Sheaf J CommRingCat.{w}) →
    (N : SheafOfModules.{w} (ringSheaf J R)) → trivSqZeroExt R N ⟶ R)

#check (inl :
  (R : Sheaf J CommRingCat.{w}) →
    (N : SheafOfModules.{w} (ringSheaf J R)) → R ⟶ trivSqZeroExt R N)

end SheafOfModules.RingedSite.TrivSqZeroExt
