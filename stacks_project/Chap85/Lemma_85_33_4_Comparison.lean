module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.GlobalSectionsComparison

/-! # Compatibility checks for total étale augmentation comparisons -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor
open scoped Simplicial

noncomputable section

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable (U : SimplicialObject (AlgebraicSpace S))
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)
variable (K : DerivedCategory.Plus (Sheaf (AlgebraicSpace.spacesEtaleTopology X)
  AddCommGrpCat.{u + 1}))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.directImageCompGlobalSectionsIso a :
    (spacesEtaleAugmentation U a).abelianDirectImage ⋙
      Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ≅
    Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.directImageCompGlobalSectionsIso_eq a :
    directImageCompGlobalSectionsIso a =
      (spacesEtaleAugmentation U a).abelianPushforwardCompΓIso)

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.constantSheafCompInverseImageIso a :
    constantSheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⋙
      (spacesEtaleAugmentation U a).abelianInverseImage ≅
    constantSheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.constantSheafCompInverseImageHom a :
    constantSheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⋙
      (spacesEtaleAugmentation U a).abelianInverseImage ⟶
    constantSheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.constantSheafCompInverseImageHom_isIso a :
    IsIso (constantSheafCompInverseImageHom a))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.rGammaDirectImageUnit a :
    ((spacesEtaleAugmentation U a).abelianDirectImage ⋙
        Sheaf.Γ (spacesEtaleTopology X) AddCommGrpCat.{u + 1}).toBoundedBelowDerived ⟶
      DerivedCategory.Plus.Qh ⋙ (EtaleDerived.plusDirectImage a ⋙ plusGlobalSections X))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.rGammaDirectImage_isRightDerived a :
    (EtaleDerived.plusDirectImage a ⋙ plusGlobalSections X).IsRightDerivedFunctor
      (rGammaDirectImageUnit a)
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.plusGlobalSectionsTotal_isRightDerived :
    (plusGlobalSectionsTotal U).IsRightDerivedFunctor
      (RightDerived.Bounded.unit
        (Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}))
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.rGammaDirectImageIso a :
    EtaleDerived.plusDirectImage a ⋙ plusGlobalSections X ≅ plusGlobalSectionsTotal U)

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.rGammaDirectImageIso_eq a :
    rGammaDirectImageIso a =
      RightDerived.natIsoOfIso DerivedCategory.Plus.Qh
        (HomotopyCategory.Plus.quasiIso
          (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}))
        (rGammaDirectImageUnit a)
        (RightDerived.Bounded.unit
          (Sheaf.Γ (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}))
        (NatIso.toBoundedBelowDerived (directImageCompGlobalSectionsIso a)))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.rGammaInverseImageComparison a :
    plusGlobalSections X ⟶ EtaleDerived.plusInverseImage a ⋙ plusGlobalSectionsTotal U)

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.rGammaInverseImageComparison_eq a :
    rGammaInverseImageComparison a =
      whiskerRight (EtaleDerived.plusDerivedUnit a) (plusGlobalSections X) ≫
        (associator (EtaleDerived.plusInverseImage a) (EtaleDerived.plusDirectImage a)
            (plusGlobalSections X)).hom ≫
        whiskerLeft (EtaleDerived.plusInverseImage a) (rGammaDirectImageIso a).hom)

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.rGammaInverseImageComparison_app a K :
    (rGammaInverseImageComparison a).app K =
      (plusGlobalSections X).map ((EtaleDerived.plusDerivedUnit a).app K) ≫
        (rGammaDirectImageIso a).hom.app ((EtaleDerived.plusInverseImage a).obj K))
