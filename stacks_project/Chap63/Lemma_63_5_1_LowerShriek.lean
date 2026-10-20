module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite.Module

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]

/- Compact-support direct image of module sheaves is a functor between the étale sites. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekModule f Λ :
  Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
    Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))

end
