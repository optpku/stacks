module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}}
variable (f : X ⟶ Y) (h : Y ⟶ Z) {g : X ⟶ Z}
variable (w : f ≫ h = g)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [IsProper h]
variable [LocallyQuasiFinite g] [LocallyOfFiniteType g]
variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]

#check (AlgebraicGeometry.Scheme.Etale.lowerShriekModule_compProperIso f h w Λ :
  lowerShriekModule g Λ ≅
    lowerShriekModule f Λ ⋙
      (smallEtalePullback h).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Z.smallEtaleTopology Y.smallEtaleTopology)

#check (AlgebraicGeometry.Scheme.Etale.liftEtaleModuleSheafHom :
  {S : Scheme.{u}} → {R : Type u} → [Ring R] →
  [S.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})] →
  {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} R)} →
  (α : (sheafCompose S.smallEtaleTopology
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F ⟶
    (sheafCompose S.smallEtaleTopology
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj G) →
  etaleModuleSheafHomLinear α → (F ⟶ G))

end AlgebraicGeometry.Scheme.Etale

end
