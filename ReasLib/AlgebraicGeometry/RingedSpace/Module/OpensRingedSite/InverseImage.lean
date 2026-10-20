module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentInverseImage
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InverseImage
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Comparison of inverse images on opens sites

The internal-ring construction of inverse image is compared with the chosen
ring-valued and module-valued inverse images on the sites of open subsets.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite

set_option backward.privateInPublic true

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.OpensInverseImage

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

private def ringCarrierEquiv (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : (Opens Y)ᵒᵖ) :
    ((opensMorphismOfTopoi f).ringDirectImage.obj R).obj.obj U ≃
      R.obj.obj ((Opens.map f.hom.base).op.obj U) :=
  (((sheafToPresheaf _ (Type u)).mapIso
    ((opensMorphismOfTopoi f).ringDirectImageForgetIso.app R)).app U).toEquiv

private def commRingCarrierEquiv
    (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : (Opens Y)ᵒᵖ) :
    ((opensMorphismOfTopoi f).commRingDirectImage.obj R).obj.obj U ≃
      R.obj.obj ((Opens.map f.hom.base).op.obj U) :=
  (((sheafToPresheaf _ (Type u)).mapIso
    ((opensMorphismOfTopoi f).commRingDirectImageForgetIso.app R)).app U).toEquiv

private theorem directImageIso_ringLaws :
    (∀ (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : (Opens Y)ᵒᵖ),
      ringCarrierEquiv f R U 0 = 0 ∧ ringCarrierEquiv f R U 1 = 1 ∧
      (∀ x y, ringCarrierEquiv f R U (x + y) =
        ringCarrierEquiv f R U x + ringCarrierEquiv f R U y) ∧
      (∀ x y, ringCarrierEquiv f R U (x * y) =
        ringCarrierEquiv f R U x * ringCarrierEquiv f R U y)) ∧
    (∀ (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
      (U : (Opens Y)ᵒᵖ),
      commRingCarrierEquiv f R U 0 = 0 ∧ commRingCarrierEquiv f R U 1 = 1 ∧
      (∀ x y, commRingCarrierEquiv f R U (x + y) =
        commRingCarrierEquiv f R U x + commRingCarrierEquiv f R U y) ∧
      (∀ x y, commRingCarrierEquiv f R U (x * y) =
        commRingCarrierEquiv f R U x * commRingCarrierEquiv f R U y)) := by
  sorry

private def ringSectionIso (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : (Opens Y)ᵒᵖ) :
    ((opensMorphismOfTopoi f).ringDirectImage.obj R).obj.obj U ≅
      R.obj.obj ((Opens.map f.hom.base).op.obj U) :=
  @RingEquiv.toRingCatIso _ _
    (((opensMorphismOfTopoi f).ringDirectImage.obj R).obj.obj U).ring
    (R.obj.obj ((Opens.map f.hom.base).op.obj U)).ring
    (show ((opensMorphismOfTopoi f).ringDirectImage.obj R).obj.obj U ≃+*
      R.obj.obj ((Opens.map f.hom.base).op.obj U) from
    { ringCarrierEquiv f R U with
      map_add' := (directImageIso_ringLaws f).1 R U |>.2.2.1
      map_mul' := (directImageIso_ringLaws f).1 R U |>.2.2.2 })

/-- Internal ring direct image agrees with direct image on the site of opens. -/
def ringDirectImageIso :
    (opensMorphismOfTopoi f).ringDirectImage ≅
      TopCat.Sheaf.pushforward RingCat.{u} f.hom.base :=
  NatIso.ofComponents (fun R ↦
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (NatIso.ofComponents (ringSectionIso f R) (by
        intro U V i
        ext x
        exact ConcreteCategory.congr_hom (NatTrans.naturality
          (((opensMorphismOfTopoi f).ringDirectImageForgetIso).hom.app R).hom i) x)))
    (by
      intro R S i
      apply (sheafToPresheaf _ RingCat.{u}).map_injective
      ext U x
      have h := (opensMorphismOfTopoi f).ringDirectImageForgetIso.hom.naturality i
      have hh := congrArg (fun t ↦ t.hom.app U) h
      exact ConcreteCategory.congr_hom hh x)

private def commRingSectionIso
    (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : (Opens Y)ᵒᵖ) :
    ((opensMorphismOfTopoi f).commRingDirectImage.obj R).obj.obj U ≅
      R.obj.obj ((Opens.map f.hom.base).op.obj U) :=
  @RingEquiv.toCommRingCatIso _ _
    (((opensMorphismOfTopoi f).commRingDirectImage.obj R).obj.obj U).commRing
    (R.obj.obj ((Opens.map f.hom.base).op.obj U)).commRing
    (show ((opensMorphismOfTopoi f).commRingDirectImage.obj R).obj.obj U ≃+*
      R.obj.obj ((Opens.map f.hom.base).op.obj U) from
    { commRingCarrierEquiv f R U with
      map_add' := (directImageIso_ringLaws f).2 R U |>.2.2.1
      map_mul' := (directImageIso_ringLaws f).2 R U |>.2.2.2 })

/-- Internal commutative-ring direct image agrees with direct image on opens. -/
def commRingDirectImageIso :
    (opensMorphismOfTopoi f).commRingDirectImage ≅
      TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base :=
  NatIso.ofComponents (fun R ↦
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (NatIso.ofComponents (commRingSectionIso f R) (by
        intro U V i
        ext x
        exact ConcreteCategory.congr_hom (NatTrans.naturality
          (((opensMorphismOfTopoi f).commRingDirectImageForgetIso).hom.app R).hom i) x)))
    (by
      intro R S i
      apply (sheafToPresheaf _ CommRingCat.{u}).map_injective
      ext U x
      have h := (opensMorphismOfTopoi f).commRingDirectImageForgetIso.hom.naturality i
      have hh := congrArg (fun t ↦ t.hom.app U) h
      exact ConcreteCategory.congr_hom hh x)

/-- Internal commutative-ring inverse image agrees canonically with pullback on opens. -/
def commRingInverseImageIso :
    (opensMorphismOfTopoi f).commRingInverseImage ≅
      TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base :=
  Adjunction.leftAdjointUniq
    (((opensMorphismOfTopoi f).commRingInverseImageAdjunction).ofNatIsoRight
      (commRingDirectImageIso f))
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base)

private def chosenCoefficientIso (B : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}) :
    ringSheaf.{u, u, u} (Opens.grothendieckTopology X) ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj B) ≅
      (opensMorphismOfTopoi f).ringInverseImage.obj (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B) :=
  ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
    ((commRingInverseImageIso f).app B)).symm ≪≫
      CotangentComplex.InverseImage.coefficientIso (opensMorphismOfTopoi f)

private theorem coefficientUnit_commutes
    (B : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}) :
    (opensMorphismOfTopoi f).ringAdjunction.unit.app (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B) ≫
      (opensMorphismOfTopoi f).ringDirectImage.map (chosenCoefficientIso f B).inv ≫
      (ringDirectImageIso f).hom.app
        (ringSheaf.{u, u, u} (Opens.grothendieckTopology X) ((TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj B)) =
      InverseImage.structureMap.{u, u} (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X) (Opens.map f.hom.base) B := by
  sorry

private def moduleRightUnderlyingIso
    (B : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}) :
    (SheafOfModules.restrictScalars (chosenCoefficientIso f B).inv ⋙
        (opensMorphismOfTopoi f).moduleRightOver (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B)) ⋙
          Sheaf.InternalModule.ToInternal.underlying (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B) ≅
      SheafOfModules.pushforward (InverseImage.structureMap.{u, u} (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X) (Opens.map f.hom.base) B) ⋙
        Sheaf.InternalModule.ToInternal.underlying (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.restrictScalars (chosenCoefficientIso f B).inv)
      ((opensMorphismOfTopoi f).moduleRightOverForgetIso (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B))

private theorem moduleRightIso_linear
    (B : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}) :
    (∀ M U (x y :
      ((SheafOfModules.restrictScalars (chosenCoefficientIso f B).inv ⋙
        (opensMorphismOfTopoi f).moduleRightOver (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B)).obj M).val.obj U),
      Sheaf.InternalModule.underlyingApp (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B)
        ((moduleRightUnderlyingIso f B).hom.app M) U (x + y) =
      Sheaf.InternalModule.underlyingApp (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B)
        ((moduleRightUnderlyingIso f B).hom.app M) U x +
      Sheaf.InternalModule.underlyingApp (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B)
        ((moduleRightUnderlyingIso f B).hom.app M) U y) ∧
    (∀ M U (r : (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B).obj.obj U) (x :
      ((SheafOfModules.restrictScalars (chosenCoefficientIso f B).inv ⋙
        (opensMorphismOfTopoi f).moduleRightOver (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B)).obj M).val.obj U),
      Sheaf.InternalModule.underlyingApp (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B)
        ((moduleRightUnderlyingIso f B).hom.app M) U (r • x) =
      r • Sheaf.InternalModule.underlyingApp (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B)
        ((moduleRightUnderlyingIso f B).hom.app M) U x) := by
  have h := coefficientUnit_commutes f B
  sorry

private def moduleRightIso
    (B : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}) :
    SheafOfModules.restrictScalars (chosenCoefficientIso f B).inv ⋙
        (opensMorphismOfTopoi f).moduleRightOver (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B) ≅
      SheafOfModules.pushforward (InverseImage.structureMap.{u, u} (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X) (Opens.map f.hom.base) B) :=
  Sheaf.InternalModule.functorIsoOfUnderlying (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B)
    (moduleRightUnderlyingIso f B) (moduleRightIso_linear f B).1
      (moduleRightIso_linear f B).2

private def moduleComparisonAdjunction
    (B : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}) :=
  (((opensMorphismOfTopoi f).moduleAdjunction (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B)).comp
    (SheafOfModules.Restriction.equivalenceOfIso
      (chosenCoefficientIso f B).symm).toAdjunction).ofNatIsoRight (moduleRightIso f B)

/-- The chosen inverse image of modules agrees with internal inverse image after
transport to the chosen coefficient sheaf. -/
def moduleInverseImageIso
    (B : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}) :
    InverseImage.modulePullback.{u, u} (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X) (Opens.map f.hom.base) B ≅
      (opensMorphismOfTopoi f).moduleInverseImage (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B) ⋙
        (SheafOfModules.restrictScalars
          (CotangentComplex.InverseImage.coefficientIso (opensMorphismOfTopoi f)).hom ⋙
        SheafOfModules.restrictScalars
          ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
            ((commRingInverseImageIso f).app B)).inv) :=
  Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction
      (InverseImage.structureMap.{u, u} (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X) (Opens.map f.hom.base) B))
    (moduleComparisonAdjunction f B) ≪≫
  Functor.isoWhiskerLeft _
    (SheafOfModules.Restriction.compIso
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
        ((commRingInverseImageIso f).app B)).inv
      (CotangentComplex.InverseImage.coefficientIso (opensMorphismOfTopoi f)).hom).symm

/-- The forward module comparison is the adjunction mate followed by the
canonical comparison for successive restrictions of scalars. -/
theorem moduleInverseImageIso_hom_app
    (B : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
    (M : SheafOfModules.{u} (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B)) :
    (moduleInverseImageIso f B).hom.app M =
      (Adjunction.leftAdjointUniq
        (SheafOfModules.pullbackPushforwardAdjunction
          (InverseImage.structureMap.{u, u} (J := Opens.grothendieckTopology Y) (K := Opens.grothendieckTopology X) (Opens.map f.hom.base) B))
        (moduleComparisonAdjunction f B)).hom.app M ≫
      (SheafOfModules.Restriction.compIso
        ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
          ((commRingInverseImageIso f).app B)).inv
        (CotangentComplex.InverseImage.coefficientIso (opensMorphismOfTopoi f)).hom).inv.app
          (((opensMorphismOfTopoi f).moduleInverseImage (ringSheaf.{u, u, u} (Opens.grothendieckTopology Y) B)).obj M) := rfl

end AlgebraicGeometry.RingedSpace.OpensInverseImage
