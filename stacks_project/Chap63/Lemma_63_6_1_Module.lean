module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.LocallyQuasiFinite.Module

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Etale

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]

/- The non-derived compact-support adjunction on étale sheaves of modules. -/
#check (AlgebraicGeometry.Scheme.Etale.lowerShriekModuleAdjunction f Λ :
  lowerShriekModule f Λ ⊣ upperShriekModule f Λ)

variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/- Module upper shriek agrees with abelian upper shriek after forgetting coefficients. -/
#check (AlgebraicGeometry.Scheme.Etale.upperShriekModule_forget f Λ :
  upperShriekModule f Λ ⋙
      sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
    sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
      upperShriek f)

end
