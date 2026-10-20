module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom

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
    AlgebraicSpace.internalCommRingInverseImage f ⋙
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

/-- Pushouts of commutative-ring sheaves exist on the small étale site of an algebraic space. -/
instance hasPushouts_smallEtale_commRingCat {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasPushouts (Sheaf (smallEtaleTopology X) CommRingCat.{u}) :=
  sorry

/-- Inverse image of `𝒪_X`-algebras along `f : Y ⟶ X`, as a functor on under-categories. -/
def inverseImageUnder {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Under (commStructureSheaf X) ⥤
      Under ((pullbackSheafFunctor f).obj (commStructureSheaf X)) :=
  Under.post (pullbackSheafFunctor f)

/-- The object map of `inverseImageUnder f` applies `pullbackSheafFunctor f` to the structure
morphism. -/
theorem inverseImageUnder_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : Under (commStructureSheaf X)) :
    (inverseImageUnder f).obj A = Under.mk ((pullbackSheafFunctor f).map A.hom) :=
  rfl

/-- Pullback of `𝒪_X`-algebras along `f : Y ⟶ X`, as a functor on the ambient under
categories, by inverse image of commutative-ring sheaves followed by sheaf pushout along
`AlgebraicSpace.commInverseImageStructureSheafMap f`. -/
def pullbackUnder {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    Under (commStructureSheaf X) ⥤ Under (commStructureSheaf Y) :=
  inverseImageUnder f ⋙ Under.pushout (AlgebraicSpace.commInverseImageStructureSheafMap f)

/-- The object map of `pullbackUnder f` is scalar extension of the inverse image. -/
theorem pullbackUnder_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : Under (commStructureSheaf X)) :
    (pullbackUnder f).obj A =
      (Under.pushout (AlgebraicSpace.commInverseImageStructureSheafMap f)).obj ((inverseImageUnder f).obj A) :=
  rfl

/-- The underlying commutative-ring sheaf of an ambient algebra pullback. -/
abbrev pullbackAlgebraSheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : Under (commStructureSheaf X)) :
    Sheaf (smallEtaleTopology Y) CommRingCat.{u} :=
  ((pullbackUnder f).obj A).right

/-- `pullbackAlgebraSheaf f A` is the right object of the sheaf-pushout algebra. -/
theorem pullbackAlgebraSheaf_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : Under (commStructureSheaf X)) :
    pullbackAlgebraSheaf f A = ((pullbackUnder f).obj A).right :=
  rfl

/-- The structure morphism of the pulled-back algebra is the right coprojection of the
sheaf pushout along `AlgebraicSpace.commInverseImageStructureSheafMap f`. -/
theorem pullbackUnder_obj_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (A : Under (commStructureSheaf X)) :
    ((pullbackUnder f).obj A).hom =
      pushout.inr ((pullbackSheafFunctor f).map A.hom) (AlgebraicSpace.commInverseImageStructureSheafMap f) :=
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
