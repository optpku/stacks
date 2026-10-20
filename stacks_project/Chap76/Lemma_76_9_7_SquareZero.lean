module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.SquareZeroRealization

/-!
# Square-zero algebras on the small étale site of an algebraic space

The inverse-image comparisons, canonical kernel module, and realization conditions
are supplied by their shared mathematical owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalCommRing
open CategoryTheory.Sheaf.InternalRing
open SheafOfModules.RingedSite
open AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension

universe u

#check (AlgebraicGeometry.AlgebraicSpace.commSheafInverseImageObj :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}),
    Sheaf (smallEtaleTopology X) CommRingCat.{u})

#check (AlgebraicGeometry.AlgebraicSpace.commSheafInverseImageMap :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    {R R' : Sheaf (smallEtaleTopology Y) CommRingCat.{u}} (α : R ⟶ R'),
    commSheafInverseImageObj h R ⟶ commSheafInverseImageObj h R')

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.commSheafInverseImageObj_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}),
    commSheafInverseImageObj h R =
      fromInternalObj.{u + 1, u, u}
        ((internalCommRingInverseImage h).obj (toInternalObj.{u + 1, u, u} R)))

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.commSheafInverseImageMap_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    {R R' : Sheaf (smallEtaleTopology Y) CommRingCat.{u}} (α : R ⟶ R'),
    commSheafInverseImageMap h α =
      fromInternalMap.{u + 1, u, u}
        ((internalCommRingInverseImage h).map (toInternalMap.{u + 1, u, u} α)))

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.commInverseImageStructureSheaf_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    commInverseImageStructureSheaf f =
      commSheafInverseImageObj f (commStructureSheaf Y))

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.commInverseImageCongr :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {a b : X ⟶ Y} (h : a = b),
    commInverseImageStructureSheaf a ≅ commInverseImageStructureSheaf b)

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.commInverseImageCongr_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {a b : X ⟶ Y} (h : a = b),
    commInverseImageCongr h = eqToIso (congrArg commInverseImageStructureSheaf h))

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.inverseImageCompIso :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y),
    (morphismOfTopoi f).inverseImage ⋙ (morphismOfTopoi p).inverseImage ≅
      (morphismOfTopoi (p ≫ f)).inverseImage)

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.inverseImageCompIso_eq :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y),
    inverseImageCompIso p f =
      Adjunction.leftAdjointCompIso
        (morphismOfTopoi f).adjunction (morphismOfTopoi p).adjunction
        (morphismOfTopoi (p ≫ f)).adjunction (Modules.typePushforwardComp p f))

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.internalCommRingInverseImageCompIso :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    (p : U ⟶ X) (f : X ⟶ Y),
    internalCommRingInverseImage f ⋙ internalCommRingInverseImage p ≅
      internalCommRingInverseImage (p ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.internalCommRingInverseImageCompIso_eq :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    (p : U ⟶ X) (f : X ⟶ Y),
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
          (inverseImageCompIso p f))

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.commSheafInverseImageCompIso :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}),
    commSheafInverseImageObj p (commSheafInverseImageObj f R) ≅
      commSheafInverseImageObj (p ≫ f) R)

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.commSheafInverseImageCompIso_eq :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}),
    commSheafInverseImageCompIso p f R =
      fromInternal.{u + 1, u, u}.mapIso
        ((internalCommRingInverseImage p).mapIso
            (fromToIso.{u + 1, u, u}.app
              ((internalCommRingInverseImage f).obj (toInternalObj.{u + 1, u, u} R))) ≪≫
          (internalCommRingInverseImageCompIso p f).app
            (toInternalObj.{u + 1, u, u} R)))

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.algebraMap :
  ∀ {S : Scheme.{u}} {B X X' : AlgebraicSpace S}
    (i : X ⟶ X') (sX : X ⟶ B) (sX' : X' ⟶ B) (h : i ≫ sX' = sX),
    commInverseImageStructureSheaf sX ⟶ commInverseImageStructureSheaf i)

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.algebraMap_eq :
  ∀ {S : Scheme.{u}} {B X X' : AlgebraicSpace S}
    (i : X ⟶ X') (sX : X ⟶ B) (sX' : X' ⟶ B) (h : i ≫ sX' = sX),
    algebraMap i sX sX' h =
      (commInverseImageCongr h.symm).hom ≫
        (commSheafInverseImageCompIso i sX' (commStructureSheaf B)).inv ≫
        commSheafInverseImageMap i (commInverseImageStructureSheafMap sX'))

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.kernelModule :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π),
    RingedSite.ModuleCat.{u} (commRingedSite X))

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.kernelModule_eq :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π),
    kernelModule π hπ =
      @KernelIdeal.IsSquareZero.targetModule.{u + 1, u, u}
        (smallEtaleSite X) _ (smallEtaleTopology X) _ A (commStructureSheaf X) π
        _ _ _ _ hπ (KernelIdeal.quotientComparison_isIso π))

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.kernelModuleForgetIso_eq :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π),
    kernelModuleForgetIso π hπ =
      @KernelIdeal.IsSquareZero.targetModuleForgetIso.{u + 1, u, u}
        (smallEtaleSite X) _ (smallEtaleTopology X) _ A (commStructureSheaf X) π
        _ _ _ _ hπ (KernelIdeal.quotientComparison_isIso π))

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.IsRealization :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} (f : X ⟶ B)
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π)
    (α : commInverseImageStructureSheaf f ⟶ A)
    (hα : α ≫ π = commInverseImageStructureSheafMap f)
    {X' : AlgebraicSpace S} (i : X ⟶ X') (s' : X' ⟶ B)
    (φ : commInverseImageStructureSheaf i ⟶ A),
    Prop)

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.IsRealization.of :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} (f : X ⟶ B)
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π)
    (α : commInverseImageStructureSheaf f ⟶ A)
    (hα : α ≫ π = commInverseImageStructureSheafMap f)
    {X' : AlgebraicSpace S} (i : X ⟶ X') (s' : X' ⟶ B)
    (φ : commInverseImageStructureSheaf i ⟶ A)
    (h_first : IsFirstOrderThickening i) (h_over : i ≫ s' = f) (h_iso : IsIso φ)
    (h_surj : φ ≫ π = commInverseImageStructureSheafMap i)
    (h_alg : α = algebraMap i f s' h_over ≫ φ),
    IsRealization f A π hπ α hα i s' φ)

#check (AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension.isRealization_iff :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} (f : X ⟶ B)
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π)
    (α : commInverseImageStructureSheaf f ⟶ A)
    (hα : α ≫ π = commInverseImageStructureSheafMap f)
    {X' : AlgebraicSpace S} (i : X ⟶ X') (s' : X' ⟶ B)
    (φ : commInverseImageStructureSheaf i ⟶ A),
    IsRealization f A π hπ α hα i s' φ ↔
      IsFirstOrderThickening i ∧
        ∃ h_over : i ≫ s' = f,
          IsIso φ ∧ φ ≫ π = commInverseImageStructureSheafMap i ∧
            α = algebraMap i f s' h_over ≫ φ)
