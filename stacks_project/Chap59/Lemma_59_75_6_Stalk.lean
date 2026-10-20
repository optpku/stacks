module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Stalk

open CategoryTheory AlgebraicGeometry

universe u

@[expose] public section

#check (AlgebraicGeometry.Scheme.étaleModuleStalk :
  ∀ {S : Scheme.{u}} {Λ : Type u} [Ring Λ] (sbar : Scheme.GeometricPoint S)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)), ModuleCat.{u} Λ)

#check (AlgebraicGeometry.Scheme.étaleModuleStalk_forget :
  ∀ {S : Scheme.{u}} {Λ : Type u} [Ring Λ] (sbar : Scheme.GeometricPoint S)
    (F : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ))
    [S.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget (ModuleCat.{u} Λ))],
    (CategoryTheory.forget (ModuleCat.{u} Λ)).obj (Scheme.étaleModuleStalk sbar F) ≃
      Scheme.Etale.stalk sbar
        ((sheafCompose S.smallEtaleTopology
            (CategoryTheory.forget (ModuleCat.{u} Λ))).obj F).obj)
