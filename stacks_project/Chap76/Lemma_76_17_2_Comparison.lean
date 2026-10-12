/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import stacks_project.Chap76.Definition_76_6_5_Conormal
public import stacks_project.Chap76.Definition_76_7_2_Differentials
public import stacks_project.Chap76.Lemma_76_17_1_Difference

/-!
# Comparing inverse-image presentations of the structure sheaf

The canonical ringed-topos inverse image and the site inverse image represent
the same left adjoint. Their comparison is constructed from the site unit via
the topos adjunction and the existing internal-commutative-ring equivalence.
It preserves the actual structure map, and changes a derivation's relative-base
certificate without changing its underlying additive maps.
-/
@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Sheaf.InternalCommRing
open CategoryTheory.Sheaf.InternalRing
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
variable {S : Scheme.{u}}

/-- The underlying Hom equivalence composes geometric transposition with the
actual direct-image isomorphism on the target. -/
def siteCommRingUnderlyingHomEquiv {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (A : Sheaf (smallEtaleTopology Y) CommRingCat.{u})
    (B : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    ((morphismOfTopoi f).inverseImage.obj ((commRingUnderlying Y).obj A) ⟶
      (commRingUnderlying X).obj B) ≃
    ((commRingUnderlying Y).obj A ⟶
      (commRingUnderlying Y).obj ((commRingPushforward f).obj B)) :=
  ((morphismOfTopoi f).adjunction.homEquiv _ _).trans
    ((commRingPushforwardUnderlyingIso f).app B).symm.homToEquiv

/-- Forward transposition retains the geometric adjunction map on all sections. -/
def siteCommRingMate {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (h : (commRingInverseImage f).obj A ⟶ B) : A ⟶ (commRingPushforward f).obj B :=
  commRingHomOfUnderlying
    (siteCommRingUnderlyingHomEquiv f A B ((commRingUnderlying X).map h))
    sorry sorry sorry sorry

/-- Reverse transposition retains the inverse geometric Hom map on all sections. -/
def siteCommRingUnmate {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (g : A ⟶ (commRingPushforward f).obj B) : (commRingInverseImage f).obj A ⟶ B :=
  commRingHomOfUnderlying
    ((siteCommRingUnderlyingHomEquiv f A B).symm ((commRingUnderlying Y).map g))
    sorry sorry sorry sorry

/-- Forgetting the forward ring map gives exactly the type-valued transpose. -/
theorem siteCommRingMate_underlying {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (h : (commRingInverseImage f).obj A ⟶ B) :
    (commRingUnderlying Y).map (siteCommRingMate f h) =
      (morphismOfTopoi f).adjunction.homEquiv _ _ ((commRingUnderlying X).map h) ≫
        (commRingPushforwardUnderlyingIso f).inv.app B := rfl

/-- Forgetting the reverse ring map gives exactly the inverse type-valued transpose. -/
theorem siteCommRingUnmate_underlying {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (g : A ⟶ (commRingPushforward f).obj B) :
    (commRingUnderlying X).map (siteCommRingUnmate f g) =
      ((morphismOfTopoi f).adjunction.homEquiv _ _).symm
        ((commRingUnderlying Y).map g ≫ (commRingPushforwardUnderlyingIso f).hom.app B) := rfl

/-- The two geometric transposes are mutually inverse on commutative-ring morphisms. -/
def siteCommRingHomEquiv {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (A : Sheaf (smallEtaleTopology Y) CommRingCat.{u})
    (B : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    ((commRingInverseImage f).obj A ⟶ B) ≃ (A ⟶ (commRingPushforward f).obj B) where
  toFun := siteCommRingMate f
  invFun := siteCommRingUnmate f
  left_inv h := by
    apply (sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
      sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).map_injective
    exact (siteCommRingUnderlyingHomEquiv f A B).symm_apply_apply ((commRingUnderlying X).map h)
  right_inv g := by
    apply (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
      sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).map_injective
    exact (siteCommRingUnderlyingHomEquiv f A B).apply_symm_apply ((commRingUnderlying Y).map g)

/-- The geometric commutative-ring adjunction has the displayed transpose maps. -/
def siteCommRingAdjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commRingInverseImage f ⊣ commRingPushforward f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := siteCommRingHomEquiv f
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- Forget a direct-image commutative-ring map using the specified pushforward comparisons. -/
def underlyingCommRingPushforwardMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {A : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
    {B : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (g : A ⟶ (commRingPushforward f).obj B) :
    CommRingObjects.carrier (smallEtaleTopology Y) (CategoryTheory.Sheaf.InternalCommRing.toInternalObj.{u + 1, u, u} A) ⟶
      (morphismOfTopoi f).pushforward.obj
        (CommRingObjects.carrier (smallEtaleTopology X) (CategoryTheory.Sheaf.InternalCommRing.toInternalObj.{u + 1, u, u} B)) :=
  (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).map
      ((sheafCompose (smallEtaleTopology Y)
        (forget₂ CommRingCat.{u} RingCat.{u})).map g) ≫
    (sheafCompose (smallEtaleTopology Y) (forget RingCat.{u})).map
      ((commRingPushforwardForgetIso f).hom.app B) ≫
    (ringPushforwardForgetIso f).hom.app
      ((sheafCompose (smallEtaleTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj B)

/-- The canonical-to-site inverse-image comparison, the transpose of the site unit. -/
def canonicalInverseImageToSite {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commInverseImageStructureSheaf f ⟶
      (commRingInverseImage f).obj (commRingStructureSheaf Y) :=
  CategoryTheory.Sheaf.InternalCommRing.fromInternalMap
    (@CommRingObjCat.Hom.mk (Sheaf (smallEtaleTopology X) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
      ((internalCommRingInverseImage f).obj
        (toInternalObj.{u + 1, u, u} (commStructureSheaf Y)))
      (toInternalObj.{u + 1, u, u}
        ((commRingInverseImage f).obj (commRingStructureSheaf Y)))
      (((morphismOfTopoi f).adjunction.homEquiv
        (CommRingObjects.carrier (smallEtaleTopology Y)
          (toInternalObj.{u + 1, u, u} (commStructureSheaf Y)))
        (CommRingObjects.carrier (smallEtaleTopology X)
          (toInternalObj.{u + 1, u, u}
            ((commRingInverseImage f).obj (commRingStructureSheaf Y))))).symm
        (underlyingCommRingPushforwardMap f
          ((siteCommRingAdjunction f).unit.app (commRingStructureSheaf Y))))
      sorry) ≫
    (CategoryTheory.Sheaf.InternalCommRing.toFromIso.{u + 1, u, u}).hom.app
      ((commRingInverseImage f).obj (commRingStructureSheaf Y))

/-- The specified comparison is the mate of the site inverse-image unit.
The finite-product lift of the topos adjunction and uniqueness of left adjoints
make this map invertible; no arbitrary isomorphism is chosen as input. -/
instance canonicalInverseImageToSite_isIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsIso (canonicalInverseImageToSite f) := by
  sorry

/-- The unit-mate comparison identifies the two actual structure morphisms. -/
theorem canonicalInverseImageToSite_comp {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    canonicalInverseImageToSite f ≫ inverseImageStructureSheafHom f =
      commInverseImageStructureSheafMap f := by
  sorry

/-- The inverse comparison carries the canonical structure map to the site structure map. -/
theorem canonicalInverseImageToSite_inv_comp {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (asIso (canonicalInverseImageToSite f)).inv ≫ commInverseImageStructureSheafMap f =
      inverseImageStructureSheafHom f := by
  rw [← canonicalInverseImageToSite_comp f]
  simp

/-- Both derivation interfaces now use the canonical relative-base map.
Preserve the additive derivation and its actual annihilation certificate;
the separate canonical-to-site comparison remains available above. -/
def ofCanonicalDerivation {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules)
    (D : Hom.derivations f F) : derivations f F where
  d := D.d
  d_mul := by intro U a b; exact D.d_mul a b
  d_map := by intro U V g a; exact D.d_map g a
  d_app := by intro U a; exact D.d_app a

/-- Converting the relative-base certificate leaves every value of the derivation unchanged. -/
theorem ofCanonicalDerivation_apply {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules)
    (D : Hom.derivations f F) (U : (smallEtaleSite X)ᵒᵖ)
    (a : (commStructureSheaf X).obj.obj U) :
    (ofCanonicalDerivation f F D).d a = D.d a := rfl

/-- The comparison loses no derivation data. -/
theorem ofCanonicalDerivation_injective {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) : Function.Injective (ofCanonicalDerivation f F) := by
  intro D E h
  ext U a
  exact congrArg (fun q ↦ q.d (X := U) a) h
end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
