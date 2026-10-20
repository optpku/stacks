module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Difference

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.Thickening
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

/-- Restriction of additive sheaves to the small étale site. -/
abbrev restrictSpacesAdd {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (smallEtaleToSpaces X).sheafPushforwardContinuous AddCommGrpCat.{u}
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- Relative derivations into a module on the small étale site. -/
abbrev derivations {S : Scheme.{u}} {Y B : AlgebraicSpace S}
    (sY : Y ⟶ B) (F : Y.Modules) :=
  Hom.derivations sY F

/-- Forget the additive structure of a sheaf on the small étale site. -/
abbrev forgetSpacesAddType {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  EtaleAdditive.ForgetComparison.forgetAdd X

/-- Equip a specified underlying sheaf map with its additive-homomorphism law. -/
def addHomOfType {S : Scheme.{u}} {X : AlgebraicSpace S}
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u}}
    (f : (forgetSpacesAddType X).obj F ⟶ (forgetSpacesAddType X).obj G)
    (hf : typeHomIsAdditive f) : F ⟶ G :=
  EtaleAdditive.ForgetComparison.homOfUnderlying f hf

/-- Restricting an underlying additive ring sheaf agrees with forgetting after restriction. -/
def restrictForgetRingIso {S : Scheme.{u}} (X : AlgebraicSpace S)
    (R : Sheaf (spacesEtaleTopology X) RingCat.{u}) :
    (restrictSpacesAdd X).obj ((forgetSpacesRing X).obj R) ≅
      (sheafCompose (smallEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})).obj
        (((smallEtaleToSpaces X).sheafPushforwardContinuous RingCat.{u}
          (smallEtaleTopology X) (spacesEtaleTopology X)).obj R) :=
  (EtaleAdditive.continuousComposeIso (smallEtaleToSpaces X)
    (forget₂ RingCat AddCommGrpCat.{u}) (smallEtaleTopology X)
    (spacesEtaleTopology X)).symm.app R

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.conormalInclusion :
  ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsFirstOrderThickening i],
    (SheafOfModules.toSheaf (structureSheaf X)).obj (Hom.conormalSheaf i) ⟶
      (EtaleAdditive.restriction X).obj ((forgetSpacesRing X).obj (closedStructureSheaf i)))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.factorizationMap :
  ∀ {S : Scheme.{u}} {X X' Y Y' B : AlgebraicSpace S} (sY : Y ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX]
    (D : Hom.derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX))),
    (EtaleAdditive.restriction X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf a iY)) ⟶
      (EtaleAdditive.restriction X).obj ((forgetSpacesRing X).obj (closedStructureSheaf iX)))

