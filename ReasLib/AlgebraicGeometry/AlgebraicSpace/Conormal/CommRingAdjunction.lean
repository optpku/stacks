module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Algebra

/-!
# Canonical commutative-ring adjunction for conormal comparisons

Transport the actual geometric adjunction through internal commutative rings,
then compare its right adjoint with the canonical small-chart direct image.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra
variable {S : Scheme.{u}}

/-- Direct image on internal commutative rings is induced by the actual type direct image. -/
noncomputable def internalCommRingPushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    CategoryTheory.Sheaf.InternalCommRing.CommRingObjects.{u + 1, u, u} (smallEtaleTopology X) ⥤
      CategoryTheory.Sheaf.InternalCommRing.CommRingObjects.{u + 1, u, u} (smallEtaleTopology Y) :=
  @Functor.mapCommRingOfFiniteProducts
    (Sheaf (smallEtaleTopology X) (Type u)) _ _
      (CategoryTheory.Sheaf.InternalRing.sheafBraidedCategory (smallEtaleTopology X))
    (Sheaf (smallEtaleTopology Y) (Type u)) _ _
      (CategoryTheory.Sheaf.InternalRing.sheafBraidedCategory (smallEtaleTopology Y))
    (morphismOfTopoi f).pushforward
      (LeftExactAdjunction.pushforwardPreservesFiniteProducts (morphismOfTopoi f))

/-- The direct-image presentation obtained from the equivalence with internal rings. -/
noncomputable def internalCommRingSheafPushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} ⥤
      Sheaf (smallEtaleTopology Y) CommRingCat.{u} :=
  CategoryTheory.Sheaf.InternalCommRing.toInternal.{u + 1, u, u} ⋙ internalCommRingPushforward f ⋙
    CategoryTheory.Sheaf.InternalCommRing.fromInternal.{u + 1, u, u}

/-- The internal-ring presentation has the specified direct image on underlying types. -/
noncomputable def internalCommRingPushforwardUnderlyingIso {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    internalCommRingSheafPushforward f ⋙ commRingUnderlying Y ≅
      commRingUnderlying X ⋙ typePushforward f :=
  NatIso.ofComponents
    (fun R ↦
      CategoryTheory.Sheaf.InternalCommRing.fromInternalForgetIso.{u + 1, u, u}.app
          ((internalCommRingPushforward f).obj
            (CategoryTheory.Sheaf.InternalCommRing.toInternal.{u + 1, u, u}.obj R)) ≪≫
        (@Functor.mapCommRingOfFiniteProductsForgetIso
          (Sheaf (smallEtaleTopology X) (Type u)) _ _
            (CategoryTheory.Sheaf.InternalRing.sheafBraidedCategory (smallEtaleTopology X))
          (Sheaf (smallEtaleTopology Y) (Type u)) _ _
            (CategoryTheory.Sheaf.InternalRing.sheafBraidedCategory (smallEtaleTopology Y))
          (morphismOfTopoi f).pushforward
            (LeftExactAdjunction.pushforwardPreservesFiniteProducts (morphismOfTopoi f))).app
              (CategoryTheory.Sheaf.InternalCommRing.toInternal.{u + 1, u, u}.obj R) ≪≫
        (typePushforward f).mapIso
          (CategoryTheory.Sheaf.InternalCommRing.toInternalForgetIso.{u + 1, u, u}.app R))
    sorry

/-- Concrete section maps identify the internal-ring and canonical direct images. -/
noncomputable def internalCommRingPushforwardIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    internalCommRingSheafPushforward f ≅ commRingPushforward f :=
  let e := internalCommRingPushforwardUnderlyingIso f ≪≫
    (commRingPushforwardUnderlyingIso f).symm
  NatIso.ofComponents
    (fun R ↦
      { hom := commRingHomOfUnderlying (e.hom.app R) sorry sorry sorry sorry
        inv := commRingHomOfUnderlying (e.inv.app R) sorry sorry sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The original geometric unit and counit act on internal commutative rings. -/
noncomputable def internalCommRingPullbackAdjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    internalCommRingInverseImage f ⊣ internalCommRingPushforward f :=
  @Functor.mapCommRingOfFiniteProductsAdjunction
    (Sheaf (smallEtaleTopology Y) (Type u)) _ _
      (CategoryTheory.Sheaf.InternalRing.sheafBraidedCategory (smallEtaleTopology Y))
    (Sheaf (smallEtaleTopology X) (Type u)) _ _
      (CategoryTheory.Sheaf.InternalRing.sheafBraidedCategory (smallEtaleTopology X))
    (morphismOfTopoi f).inverseImage inferInstance
    (morphismOfTopoi f).pushforward
      (LeftExactAdjunction.pushforwardPreservesFiniteProducts (morphismOfTopoi f))
    (morphismOfTopoi f).adjunction

/-- Inverse image of commutative-ring sheaves is left adjoint to direct image. -/
noncomputable def commRingInverseImageAdjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingInverseImage f ⊣ commRingPushforward f :=
  ((((CategoryTheory.Sheaf.InternalCommRing.equivalence.{u + 1, u, u}
      (J := smallEtaleTopology Y)).toAdjunction.comp
      (internalCommRingPullbackAdjunction f)).comp
      (CategoryTheory.Sheaf.InternalCommRing.equivalence.{u + 1, u, u}
        (J := smallEtaleTopology X)).symm.toAdjunction).ofNatIsoLeft
    (Functor.associator _ _ _)).ofNatIsoRight (internalCommRingPushforwardIso f)


/-- Lift a commutative-ring cone using the concrete small-chart limit on underlying types. -/
def commRingPushforwardConeLift {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology X) CommRingCat.{u}) (V : smallEtaleSite Y)
    (c : Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj V))
      (smallEtaleToSpaces X).op ⋙ R.obj)) :
    c.pt ⟶ ((commRingPushforward f).obj R).obj.obj (op V) :=
  @CommRingCat.ofHom c.pt (((commRingPushforward f).obj R).obj.obj (op V))
    (inferInstanceAs (CommRing c.pt))
    (inferInstanceAs (CommRing (((commRingPushforward f).obj R).obj.obj (op V))))
    { toFun := fun x ↦ ((commRingPushforwardUnderlyingIso f).inv.app R).hom.app (op V)
        (EtaleTopos.allChartLift X ((commRingUnderlying X).obj R) ((etaleBaseChange f).obj V)
          ((forget CommRingCat.{u}).mapCone c) x)
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- Inverse image of commutative-ring sheaves along a composite is the composite of the
inverse images. -/
noncomputable def commRingInverseImageCompIso {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    commRingInverseImage g ⋙ commRingInverseImage f ≅ commRingInverseImage (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (commRingInverseImageAdjunction g) (commRingInverseImageAdjunction f)
    (commRingInverseImageAdjunction (f ≫ g)) (AlgebraicSpace.commRingPushforwardComp f g)

end AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra
