module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Module.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LocallyQuasiFinite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition

/-!
# Composition of derived étale lower shriek
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [IsSeparated g] [LocallyQuasiFinite g] [LocallyOfFiniteType g]
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

variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived compact-support identification
`f_! ⋙ g_! ≅ (f ≫ g)_!` on `D(-, Λ)`. -/
def lowerShriekModuleDerivedCompIso :
    lowerShriekModuleDerived f Λ ⋙ lowerShriekModuleDerived g Λ ≅
      lowerShriekModuleDerived (f ≫ g) Λ :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (lowerShriekModule f Λ))
      (ExactFunctor.of (lowerShriekModule g Λ))).symm ≪≫
    Functor.MapDerivedCategory.functorIso (lowerShriekModuleCompIso f g Λ)

/-- The forward map of `lowerShriekModuleDerivedCompIso` is the exact-derived
composition comparison conjugated by `mapDerivedCategory` of
`lowerShriekModuleCompIso`. -/
theorem lowerShriekModuleDerivedCompIso_hom :
    (lowerShriekModuleDerivedCompIso f g Λ).hom =
      (ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of (lowerShriekModule f Λ))
          (ExactFunctor.of (lowerShriekModule g Λ))).symm.hom ≫
        (Functor.MapDerivedCategory.functorIso
          (lowerShriekModuleCompIso f g Λ)).hom := sorry

end AlgebraicGeometry.Scheme.Etale

end
