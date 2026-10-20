module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.Algebra.Category.CommRing.Internal
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom

/-!
# Inverse image of commutative-ring sheaves on algebraic spaces

Inverse image on small étale sites acts on commutative-ring sheaves and their morphisms,
and has canonical comparisons for equality and composition of geometric morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalCommRing
open CategoryTheory.Sheaf.InternalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Inverse image of a commutative-ring sheaf along a morphism of algebraic spaces. -/
def commSheafInverseImageObj {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  fromInternalObj.{u + 1, u, u}
    ((internalCommRingInverseImage h).obj (toInternalObj.{u + 1, u, u} R))

/-- Inverse image of a morphism of commutative-ring sheaves along a morphism of algebraic
spaces. -/
def commSheafInverseImageMap {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    {R R' : Sheaf (smallEtaleTopology Y) CommRingCat.{u}} (α : R ⟶ R') :
    commSheafInverseImageObj h R ⟶ commSheafInverseImageObj h R' :=
  fromInternalMap.{u + 1, u, u}
    ((internalCommRingInverseImage h).map (toInternalMap.{u + 1, u, u} α))

namespace SquareZeroExtension

/-- `commSheafInverseImageObj h R` is internal inverse image of `R` along `h`. -/
theorem commSheafInverseImageObj_eq {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    commSheafInverseImageObj h R =
      fromInternalObj.{u + 1, u, u}
        ((internalCommRingInverseImage h).obj (toInternalObj.{u + 1, u, u} R)) :=
  rfl

/-- `commSheafInverseImageMap h α` is internal inverse image of `α` along `h`. -/
theorem commSheafInverseImageMap_eq {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    {R R' : Sheaf (smallEtaleTopology Y) CommRingCat.{u}} (α : R ⟶ R') :
    commSheafInverseImageMap h α =
      fromInternalMap.{u + 1, u, u}
        ((internalCommRingInverseImage h).map (toInternalMap.{u + 1, u, u} α)) :=
  rfl

/-- The inverse-image structure sheaf `f⁻¹𝒪_Y` is inverse image of `𝒪_Y`. -/
theorem commInverseImageStructureSheaf_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commInverseImageStructureSheaf f =
      commSheafInverseImageObj f (commStructureSheaf Y) :=
  rfl

/-- Equal morphisms of algebraic spaces induce equal inverse-image structure sheaves. -/
def commInverseImageCongr {X Y : AlgebraicSpace S} {a b : X ⟶ Y} (h : a = b) :
    commInverseImageStructureSheaf a ≅ commInverseImageStructureSheaf b :=
  eqToIso (congrArg commInverseImageStructureSheaf h)

/-- `commInverseImageCongr` is `eqToIso` of congruence on `commInverseImageStructureSheaf`. -/
theorem commInverseImageCongr_eq {X Y : AlgebraicSpace S} {a b : X ⟶ Y} (h : a = b) :
    commInverseImageCongr h = eqToIso (congrArg commInverseImageStructureSheaf h) :=
  rfl

/-- Inverse image of types along a composite morphism of algebraic spaces. -/
def inverseImageCompIso {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y) :
    (morphismOfTopoi f).inverseImage ⋙ (morphismOfTopoi p).inverseImage ≅
      (morphismOfTopoi (p ≫ f)).inverseImage :=
  Adjunction.leftAdjointCompIso
    (morphismOfTopoi f).adjunction (morphismOfTopoi p).adjunction
    (morphismOfTopoi (p ≫ f)).adjunction (Modules.typePushforwardComp p f)

/-- `inverseImageCompIso` is the left-adjoint mate of `typePushforwardComp`. -/
theorem inverseImageCompIso_eq {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y) :
    inverseImageCompIso p f =
      Adjunction.leftAdjointCompIso
        (morphismOfTopoi f).adjunction (morphismOfTopoi p).adjunction
        (morphismOfTopoi (p ≫ f)).adjunction (Modules.typePushforwardComp p f) :=
  rfl

/-- Inverse image of internal commutative rings reassociates along composition. -/
def internalCommRingInverseImageCompIso {U X Y : AlgebraicSpace S}
    (p : U ⟶ X) (f : X ⟶ Y) :
    internalCommRingInverseImage f ⋙ internalCommRingInverseImage p ≅
      internalCommRingInverseImage (p ≫ f) :=
  (@mapCommRingOfFiniteProductsCompIso
      (Sheaf (smallEtaleTopology Y) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
      (Sheaf (smallEtaleTopology X) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
      (Sheaf (smallEtaleTopology U) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U))
      (morphismOfTopoi f).inverseImage inferInstance
      (morphismOfTopoi p).inverseImage inferInstance).symm ≪≫
    @mapCommRingOfFiniteProductsNatIso
      (Sheaf (smallEtaleTopology Y) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
      (Sheaf (smallEtaleTopology U) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U))
      ((morphismOfTopoi f).inverseImage ⋙ (morphismOfTopoi p).inverseImage)
      (morphismOfTopoi (p ≫ f)).inverseImage inferInstance inferInstance
      (inverseImageCompIso p f)

/-- The internal commutative-ring comparison is induced by the inverse-image composition
isomorphism. -/
theorem internalCommRingInverseImageCompIso_eq {U X Y : AlgebraicSpace S}
    (p : U ⟶ X) (f : X ⟶ Y) :
    internalCommRingInverseImageCompIso p f =
      (@mapCommRingOfFiniteProductsCompIso
          (Sheaf (smallEtaleTopology Y) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
          (Sheaf (smallEtaleTopology X) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
          (Sheaf (smallEtaleTopology U) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U))
          (morphismOfTopoi f).inverseImage inferInstance
          (morphismOfTopoi p).inverseImage inferInstance).symm ≪≫
        @mapCommRingOfFiniteProductsNatIso
          (Sheaf (smallEtaleTopology Y) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
          (Sheaf (smallEtaleTopology U) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U))
          ((morphismOfTopoi f).inverseImage ⋙ (morphismOfTopoi p).inverseImage)
          (morphismOfTopoi (p ≫ f)).inverseImage inferInstance inferInstance
          (inverseImageCompIso p f) :=
  rfl

/-- Inverse image of commutative-ring sheaves reassociates along composition. -/
def commSheafInverseImageCompIso {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    commSheafInverseImageObj p (commSheafInverseImageObj f R) ≅
      commSheafInverseImageObj (p ≫ f) R :=
  fromInternal.{u + 1, u, u}.mapIso
    ((internalCommRingInverseImage p).mapIso
        (fromToIso.{u + 1, u, u}.app
          ((internalCommRingInverseImage f).obj (toInternalObj.{u + 1, u, u} R))) ≪≫
      (internalCommRingInverseImageCompIso p f).app
        (toInternalObj.{u + 1, u, u} R))

/-- The sheaf composition comparison is induced by the internal commutative-ring comparison. -/
theorem commSheafInverseImageCompIso_eq {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    commSheafInverseImageCompIso p f R =
      fromInternal.{u + 1, u, u}.mapIso
        ((internalCommRingInverseImage p).mapIso
            (fromToIso.{u + 1, u, u}.app
              ((internalCommRingInverseImage f).obj (toInternalObj.{u + 1, u, u} R))) ≪≫
          (internalCommRingInverseImageCompIso p f).app
            (toInternalObj.{u + 1, u, u} R)) :=
  rfl

end SquareZeroExtension

end AlgebraicGeometry.AlgebraicSpace
