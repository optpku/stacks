module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_48_1_QcAlgebra

/-!
# Pullback of quasi-coherent algebras on algebraic spaces

A morphism of algebraic spaces induces inverse image of commutative-ring sheaves on
small étale sites by transporting the left-exact type-valued inverse image through
internal commutative rings. Quasi-coherent algebras are pulled back by the sheaf
pushout of that inverse image along the inverse-image structure map `f⁻¹ 𝒪_X ⟶ 𝒪_Y`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalCommRing
open CategoryTheory.Sheaf.InternalRing
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

/-- Inverse image of commutative-ring sheaves along a morphism of algebraic spaces, obtained
by converting to internal commutative rings, applying the left-exact inverse image of
`ringedToposHom f`, and reconstructing. -/
def pullbackSheafFunctor {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} ⥤
      Sheaf (smallEtaleTopology Y) CommRingCat.{u} :=
  InternalCommRing.toInternal.{u + 1, u, u} ⋙
    (@Functor.mapCommRingOfFiniteProducts
      (Sheaf (smallEtaleTopology X) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
      (Sheaf (smallEtaleTopology Y) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
      (morphismOfTopoi f).inverseImage inferInstance) ⋙
    InternalCommRing.fromInternal.{u + 1, u, u}

/-- Inverse image of commutative-ring sheaves is internal-commutative-ring transport of
`morphismOfTopoi f`. -/
theorem pullbackSheafFunctor_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    pullbackSheafFunctor f =
      InternalCommRing.toInternal.{u + 1, u, u} ⋙
        (@Functor.mapCommRingOfFiniteProducts
          (Sheaf (smallEtaleTopology X) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
          (Sheaf (smallEtaleTopology Y) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
          (morphismOfTopoi f).inverseImage inferInstance) ⋙
        InternalCommRing.fromInternal.{u + 1, u, u} :=
  rfl

/-- Forgetting commutativity after inverse image of commutative-ring sheaves recovers
ring-valued inverse image. -/
def pullbackSheafFunctor_forgetRingIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((pullbackSheafFunctor f).obj A) ≅
      (ringedToposHom f).toTopos.ringInverseImage.obj
        ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj A) :=
  Iso.refl _

/-- Forgetting commutativity after inverse image of commutative-ring sheaves recovers
ring-valued inverse image. -/
theorem pullbackSheafFunctor_forgetRing {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((pullbackSheafFunctor f).obj A) =
      (ringedToposHom f).toTopos.ringInverseImage.obj
        ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj A) :=
  rfl

/-- The ring-valued inverse-image structure map, transported from
`(ringedToposHom f).structureMap` along the forgetful comparison of `𝒪_X`. -/
def inverseImageStructureForget {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((pullbackSheafFunctor f).obj (commRingStructureSheaf X)) ⟶
      (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (commRingStructureSheaf Y) :=
  (pullbackSheafFunctor_forgetRingIso f (commRingStructureSheaf X)).hom ≫
    (ringedToposHom f).toTopos.ringInverseImage.map
      (eqToHom (forget₂_commRingStructureSheaf X)) ≫
    (ringedToposHom f).structureMap ≫
    eqToHom (forget₂_commRingStructureSheaf Y).symm

/-- `inverseImageStructureForget f` is the transported ring-valued structure map. -/
theorem inverseImageStructureForget_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    inverseImageStructureForget f =
      (pullbackSheafFunctor_forgetRingIso f (commRingStructureSheaf X)).hom ≫
        (ringedToposHom f).toTopos.ringInverseImage.map
          (eqToHom (forget₂_commRingStructureSheaf X)) ≫
        (ringedToposHom f).structureMap ≫
        eqToHom (forget₂_commRingStructureSheaf Y).symm :=
  rfl

/-- The inverse-image structure map `f⁻¹ 𝒪_X ⟶ 𝒪_Y`, lifted from
`(ringedToposHom f).structureMap`. -/
def inverseImageStructure {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    (pullbackSheafFunctor f).obj (commRingStructureSheaf X) ⟶
      commRingStructureSheaf Y :=
  (InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing.{u + 1, u, u}).preimage
    (inverseImageStructureForget f)

/-- Forgetting commutativity of `inverseImageStructure f` recovers the transported
ring-valued structure map. -/
theorem inverseImageStructure_forget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    (sheafCompose (smallEtaleTopology Y) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (inverseImageStructure f) =
      inverseImageStructureForget f :=
  sorry

/-- Pushouts of commutative-ring sheaves exist on the small étale site of an algebraic space. -/
instance hasPushouts_smallEtale_commRingCat {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasPushouts (Sheaf (smallEtaleTopology X) CommRingCat.{u}) :=
  sorry

/-- Scalar extension along `inverseImageStructure f` exists as a pushout of sheaves of
commutative rings. -/
instance hasPushoutsAlong_inverseImageStructure {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    HasPushoutsAlong (inverseImageStructure f) :=
  inferInstance

/-- Inverse image of `𝒪_X`-algebras along `f : Y ⟶ X`, as a functor on under-categories. -/
def inverseImageUnder {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Under (commRingStructureSheaf X) ⥤
      Under ((pullbackSheafFunctor f).obj (commRingStructureSheaf X)) :=
  Under.post (pullbackSheafFunctor f)

/-- The object map of `inverseImageUnder f` applies `pullbackSheafFunctor f` to the structure
morphism. -/
theorem inverseImageUnder_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : Under (commRingStructureSheaf X)) :
    (inverseImageUnder f).obj A = Under.mk ((pullbackSheafFunctor f).map A.hom) :=
  rfl

/-- Pullback of `𝒪_X`-algebras along `f : Y ⟶ X`, as a functor on the ambient under
categories, by inverse image of commutative-ring sheaves followed by sheaf pushout along
`inverseImageStructure f`. -/
def pullbackUnder {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Under (commRingStructureSheaf X) ⥤ Under (commRingStructureSheaf Y) :=
  inverseImageUnder f ⋙ Under.pushout (inverseImageStructure f)

/-- The object map of `pullbackUnder f` is scalar extension of the inverse image. -/
theorem pullbackUnder_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : Under (commRingStructureSheaf X)) :
    (pullbackUnder f).obj A =
      (Under.pushout (inverseImageStructure f)).obj ((inverseImageUnder f).obj A) :=
  rfl

/-- The underlying commutative-ring sheaf of an ambient algebra pullback. -/
abbrev pullbackAlgebraSheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : Under (commRingStructureSheaf X)) :
    Sheaf (smallEtaleTopology Y) CommRingCat.{u} :=
  ((pullbackUnder f).obj A).right

/-- `pullbackAlgebraSheaf f A` is the right object of the sheaf-pushout algebra. -/
theorem pullbackAlgebraSheaf_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : Under (commRingStructureSheaf X)) :
    pullbackAlgebraSheaf f A = ((pullbackUnder f).obj A).right :=
  rfl

/-- The structure morphism of the pulled-back algebra is the right coprojection of the
sheaf pushout along `inverseImageStructure f`. -/
theorem pullbackUnder_obj_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : Under (commRingStructureSheaf X)) :
    ((pullbackUnder f).obj A).hom =
      pushout.inr ((pullbackSheafFunctor f).map A.hom) (inverseImageStructure f) :=
  rfl

/-- The underlying `𝒪_X`-module of an `𝒪_X`-algebra. -/
def algebraModule {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : Under (commRingStructureSheaf X)) :
    ringedSiteModuleCategory (smallEtaleTopology X) (commRingStructureSheaf X) :=
  (restrictionAlong A.hom).obj (unitModule (smallEtaleTopology X) A.right)

/-- `algebraModule A` is restriction of scalars of the unit module of `A`. -/
theorem algebraModule_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : Under (commRingStructureSheaf X)) :
    algebraModule A =
      (restrictionAlong A.hom).obj (unitModule (smallEtaleTopology X) A.right) :=
  rfl

/-- Pullback of quasi-coherent algebras remains quasi-coherent. -/
theorem pullbackUnder_mapsTo {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    qcAlgebraUnderProperty X ≤
      (qcAlgebraUnderProperty Y).inverseImage (pullbackUnder f) :=
  sorry

/-- Pullback of quasi-coherent `𝒪_X`-algebras along a morphism of algebraic spaces. -/
def pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    X.QcAlgebraUnder ⥤ Y.QcAlgebraUnder :=
  ObjectProperty.FullSubcategory.restrict (pullbackUnder f) (pullbackUnder_mapsTo f)

/-- The underlying algebra object of a pulled-back quasi-coherent algebra is the ambient
under-category pullback. -/
theorem pullback_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : X.QcAlgebraUnder) :
    ((pullback f).obj A).obj = (pullbackUnder f).obj A.obj :=
  rfl

/-- The underlying commutative-ring sheaf of a pulled-back quasi-coherent algebra is the
sheaf-pushout scalar extension of the inverse image. -/
theorem pullback_sheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : X.QcAlgebraUnder) :
    sheaf ((pullback f).obj A) = pullbackAlgebraSheaf f A.obj :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder
