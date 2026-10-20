module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.NaiveCotangent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingInverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RestrictionRing
public import Mathlib.Algebra.Homology.Additive
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtaleSheafification

/-!
# Étale localization of naive cotangent complexes

A commutative square with étale vertical morphisms induces canonical comparisons
of coefficient sheaves, polynomial presentations, and naive cotangent complexes.
The explicit mutually inverse chain maps give an identification in the derived category.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MorphismProperty
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Modules
open Algebra Algebra.Extension Algebra.Generators
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalCommRing
open CategoryTheory.Sheaf.InternalModule
open ComplexShape
open scoped AlgebraicGeometry.AlgebraicSpace ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent

variable {S : Scheme.{u}}

/-- The object of `X_étale` obtained by postcomposing an étale chart of `U` with `p`. -/
abbrev restrictChart {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (W : (smallEtaleSite U)ᵒᵖ) : (smallEtaleSite X)ᵒᵖ :=
  op ((restrictPostcompose p).obj W.unop)

/-- Restriction of `𝒪_X` along the étale site functor of `p`, as a commutative-ring map. -/
def structureCoeff {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (W : (smallEtaleSite U)ᵒᵖ) :
    (commStructureSheaf X).obj.obj (restrictChart p W) ⟶
      (commStructureSheaf U).obj.obj W :=
  CommRingCat.ofHom ((restrictStructureMap p).hom.app W).hom

/-- Inverse of `structureCoeff`, identity on sections. -/
def structureCoeffInv {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (W : (smallEtaleSite U)ᵒᵖ) :
    (commStructureSheaf U).obj.obj W ⟶
      (commStructureSheaf X).obj.obj (restrictChart p W) :=
  CommRingCat.ofHom ((restrictStructureMapInv p).hom.app W).hom

/-- The canonical composition comparison commutes with morphisms of coefficient sheaves. -/
theorem pullbackSheafFunctorComp_naturality {U X Y : AlgebraicSpace S}
    (p : U ⟶ X) (f : X ⟶ Y)
    {A B : Sheaf (smallEtaleTopology Y) CommRingCat.{u}} (α : A ⟶ B) :
    (QcAlgebraUnder.pullbackSheafFunctor f ⋙ QcAlgebraUnder.pullbackSheafFunctor p).map α ≫
        (SquareZeroExtension.commSheafInverseImageCompIso p f B).hom =
      (SquareZeroExtension.commSheafInverseImageCompIso p f A).hom ≫
        (QcAlgebraUnder.pullbackSheafFunctor (p ≫ f)).map α :=
  sorry

/-- Inverse image of commutative-ring sheaves reassociates along composition. -/
def pullbackSheafFunctorComp {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y) :
    QcAlgebraUnder.pullbackSheafFunctor f ⋙ QcAlgebraUnder.pullbackSheafFunctor p ≅
      QcAlgebraUnder.pullbackSheafFunctor (p ≫ f) :=
  NatIso.ofComponents (SquareZeroExtension.commSheafInverseImageCompIso p f)
    (fun {_ _} α ↦ pullbackSheafFunctorComp_naturality p f α)

/-- Restriction of commutative-ring sheaves along an étale morphism, by postcomposition
on small étale sites. -/
def restrictSheaf {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} ⥤
      Sheaf (smallEtaleTopology U) CommRingCat.{u} :=
  (restrictPostcompose p).sheafPushforwardContinuous CommRingCat.{u}
    (smallEtaleTopology U) (smallEtaleTopology X)

/-- The identity on structure-sheaf sections commutes with restriction maps. -/
theorem restrictCommStructureMap_naturality {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    {W Z : (smallEtaleSite U)ᵒᵖ} (a : W ⟶ Z) :
    ((restrictSheaf p).obj (commStructureSheaf X)).obj.map a ≫ 𝟙 _ = 𝟙 _ ≫ (commStructureSheaf U).obj.map a :=
  sorry

/-- Identity-on-sections comparison `(p_small⁻¹ 𝒪_X) ⟶ 𝒪_U` of commutative-ring sheaves. -/
def restrictCommStructureMap {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictSheaf p).obj (commStructureSheaf X) ⟶ commStructureSheaf U :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := fun {_ _} a ↦ restrictCommStructureMap_naturality p a }⟩

/-- The identity on structure-sheaf sections commutes with restriction maps. -/
theorem restrictCommStructureMapInv_naturality {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    {W Z : (smallEtaleSite U)ᵒᵖ} (a : W ⟶ Z) :
    (commStructureSheaf U).obj.map a ≫ 𝟙 _ = 𝟙 _ ≫ ((restrictSheaf p).obj (commStructureSheaf X)).obj.map a :=
  sorry

/-- Identity-on-sections inverse `𝒪_U ⟶ (p_small⁻¹ 𝒪_X)` of commutative-ring sheaves. -/
def restrictCommStructureMapInv {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    commStructureSheaf U ⟶ (restrictSheaf p).obj (commStructureSheaf X) :=
  ⟨{ app := fun _ ↦ 𝟙 _
     naturality := fun {_ _} a ↦ restrictCommStructureMapInv_naturality p a }⟩

/-- The identity-on-sections structure comparisons compose to the identity. -/
theorem restrictCommStructureIso_hom_inv_id {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    restrictCommStructureMap p ≫ restrictCommStructureMapInv p = 𝟙 ((restrictSheaf p).obj (commStructureSheaf X)) :=
  sorry

/-- The identity-on-sections structure comparisons compose to the identity. -/
theorem restrictCommStructureIso_inv_hom_id {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    restrictCommStructureMapInv p ≫ restrictCommStructureMap p = 𝟙 (commStructureSheaf U) :=
  sorry

/-- The identification `p_small⁻¹ 𝒪_X ≅ 𝒪_U` of commutative-ring sheaves, given by identity
on sections. -/
def restrictCommStructureIso {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    (restrictSheaf p).obj (commStructureSheaf X) ≅ commStructureSheaf U where
  hom := restrictCommStructureMap p
  inv := restrictCommStructureMapInv p
  hom_inv_id := restrictCommStructureIso_hom_inv_id p
  inv_hom_id := restrictCommStructureIso_inv_hom_id p

/-- Forgotten étale restriction of commutative-ring sheaves agrees with ring inverse image. -/
def restrictSheafForgetRingIso {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    (sheafCompose (smallEtaleTopology U) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((restrictSheaf p).obj A) ≅
      (sheafCompose (smallEtaleTopology U) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((QcAlgebraUnder.pullbackSheafFunctor p).obj A) :=
  (eqToIso (congrArg (fun G ↦ G.obj A)
      (Functor.sheafPushforwardContinuous.compSheafCompose
        (restrictPostcompose p) (forget₂ CommRingCat.{u} RingCat.{u})
        (smallEtaleTopology U) (smallEtaleTopology X)))) ≪≫
    (EtaleTopos.restrictRingIsoInverseImage p).app
      ((sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ≪≫
    (QcAlgebraUnder.pullbackSheafFunctor_forgetRingIso p A).symm

/-- The lifted restriction comparison is natural in the commutative-ring sheaf. -/
theorem restrictSheafIsoPullbackSheaf_naturality {U X : AlgebraicSpace S}
    (p : U ⟶ X) [Etale p]
    {A B : Sheaf (smallEtaleTopology X) CommRingCat.{u}} (α : A ⟶ B) :
    (restrictSheaf p).map α ≫ ((CommRingSheaves.fullyFaithfulForgetRing.{u + 1, u, u}
        (J := smallEtaleTopology U)).preimageIso
      (restrictSheafForgetRingIso p B)).hom =
      ((CommRingSheaves.fullyFaithfulForgetRing.{u + 1, u, u}
        (J := smallEtaleTopology U)).preimageIso
      (restrictSheafForgetRingIso p A)).hom ≫ (QcAlgebraUnder.pullbackSheafFunctor p).map α :=
  sorry

/-- Étale restriction of commutative-ring sheaves is isomorphic to inverse image in the
algebra-pullback presentation. -/
def restrictSheafIsoPullbackSheaf {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p] :
    restrictSheaf p ≅ QcAlgebraUnder.pullbackSheafFunctor p :=
  NatIso.ofComponents
    (fun A ↦
      (CommRingSheaves.fullyFaithfulForgetRing.{u + 1, u, u}
          (J := smallEtaleTopology U)).preimageIso
        (restrictSheafForgetRingIso p A))
    (fun {_ _} α ↦ restrictSheafIsoPullbackSheaf_naturality p α)

/-- The inverse-image form `f⁻¹𝒪_Y` is algebra-pullback of `𝒪_Y`. -/
theorem commInverseImageStructureSheaf_eq_pullback {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commInverseImageStructureSheaf f =
      (QcAlgebraUnder.pullbackSheafFunctor f).obj (commStructureSheaf Y) :=
  rfl

/-- For an étale morphism, the inverse-image form `f⁻¹𝒪_Y` identifies with `𝒪_X`. -/
def commInverseImageStructureSheafIso_of_etale {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] :
    commInverseImageStructureSheaf f ≅ commStructureSheaf X :=
  eqToIso (commInverseImageStructureSheaf_eq_pullback f) ≪≫
    (restrictSheafIsoPullbackSheaf f).symm.app (commStructureSheaf Y) ≪≫
    restrictCommStructureIso f


/-- Evaluation of étale restriction of a commutative-ring sheaf recovers the original
sections on the postcomposed chart. -/
theorem restrictSheaf_obj_obj {U X : AlgebraicSpace S} (p : U ⟶ X) [Etale p]
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) (W : (smallEtaleSite U)ᵒᵖ) :
    ((restrictSheaf p).obj A).obj.obj W = A.obj.obj (restrictChart p W) :=
  rfl

/-- The comparison `p⁻¹ f⁻¹ 𝒪_Y ≅ g⁻¹ 𝒪_V` of coefficient sheaves of a commutative étale
square, as étale restriction of `f⁻¹𝒪_Y`. -/
def inverseImageCoeffSheafIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (restrictSheaf p).obj (commInverseImageStructureSheaf f) ≅
      commInverseImageStructureSheaf g :=
  (restrictSheafIsoPullbackSheaf p).app (commInverseImageStructureSheaf f) ≪≫
    eqToIso (congrArg (QcAlgebraUnder.pullbackSheafFunctor p).obj
      (commInverseImageStructureSheaf_eq_pullback f)) ≪≫
    (pullbackSheafFunctorComp p f).app (commStructureSheaf Y) ≪≫
    eqToIso (congrArg
      (fun h : U ⟶ Y ↦ (QcAlgebraUnder.pullbackSheafFunctor h).obj (commStructureSheaf Y))
      hcomm) ≪≫
    (pullbackSheafFunctorComp g q).symm.app (commStructureSheaf Y) ≪≫
    eqToIso (congrArg (QcAlgebraUnder.pullbackSheafFunctor g).obj
      (commInverseImageStructureSheaf_eq_pullback q).symm) ≪≫
    (QcAlgebraUnder.pullbackSheafFunctor g).mapIso
      (commInverseImageStructureSheafIso_of_etale q) ≪≫
    eqToIso (commInverseImageStructureSheaf_eq_pullback g).symm

/-- The comparison `p⁻¹ f⁻¹ 𝒪_Y ⟶ g⁻¹ 𝒪_V` of coefficient sheaves of a commutative étale
square, as étale restriction of `f⁻¹𝒪_Y`. -/
def inverseImageCoeffSheaf {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (restrictSheaf p).obj (commInverseImageStructureSheaf f) ⟶
      commInverseImageStructureSheaf g :=
  (inverseImageCoeffSheafIso p g f q hcomm).hom

/-- The objectwise coefficient map `f⁻¹𝒪_Y(jW) ⟶ g⁻¹𝒪_V(W)` of a commutative étale square. -/
def inverseImageCoeff {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    (commInverseImageStructureSheaf f).obj.obj (restrictChart p W) ⟶
      (commInverseImageStructureSheaf g).obj.obj W :=
  eqToHom (restrictSheaf_obj_obj p (commInverseImageStructureSheaf f) W).symm ≫
    (inverseImageCoeffSheaf p g f q hcomm).hom.app W

/-- The reverse objectwise coefficient map `g⁻¹𝒪_V(W) ⟶ f⁻¹𝒪_Y(jW)` of a commutative étale
square. -/
def inverseImageCoeffInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    (commInverseImageStructureSheaf g).obj.obj W ⟶
      (commInverseImageStructureSheaf f).obj.obj (restrictChart p W) :=
  (inverseImageCoeffSheafIso p g f q hcomm).inv.hom.app W ≫
    eqToHom (restrictSheaf_obj_obj p (commInverseImageStructureSheaf f) W)

/-- The polynomial-ring map of canonical presentations induced by a commutative étale square. -/
def squarePresentationRingHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    MvPolynomial ((commStructureSheaf X).obj.obj (restrictChart p W))
        ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)) →+*
      MvPolynomial ((commStructureSheaf U).obj.obj W)
        ((commInverseImageStructureSheaf g).obj.obj W) :=
  (MvPolynomial.map (inverseImageCoeff p g f q hcomm W).hom).comp
    (MvPolynomial.rename fun s ↦ (structureCoeff p W).hom s).toRingHom

/-- The polynomial comparison preserves the specified coefficient action. -/
theorem squarePresentationAlgHom_commutes {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := (inverseImageCoeff p g f q hcomm W).hom.toAlgebra

  ∀ r : (commInverseImageStructureSheaf f).obj.obj (restrictChart p W),
    squarePresentationRingHom p g f q hcomm W (algebraMap ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)) (MvPolynomial ((commStructureSheaf X).obj.obj (restrictChart p W)) ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))) r) =
      algebraMap ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)) (MvPolynomial ((commStructureSheaf U).obj.obj W) ((commInverseImageStructureSheaf g).obj.obj W)) r :=
  sorry

/-- The algebra homomorphism of canonical presentations induced by a commutative étale square. -/
def squarePresentationAlgHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :=
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := (inverseImageCoeff p g f q hcomm W).hom.toAlgebra
  ({ squarePresentationRingHom p g f q hcomm W with
      commutes' := squarePresentationAlgHom_commutes p g f q hcomm W } :
    MvPolynomial ((commStructureSheaf X).obj.obj (restrictChart p W))
        ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)) →ₐ[
      (commInverseImageStructureSheaf f).obj.obj (restrictChart p W)]
      MvPolynomial ((commStructureSheaf U).obj.obj W)
        ((commInverseImageStructureSheaf g).obj.obj W))

/-- The kernel of the canonical presentation is compatible with the square comparison. -/
theorem squarePresentationKer_le_comap {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
    letI := inverseImageAlgebra f (restrictChart p W)
    -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
    letI := inverseImageAlgebra g W
    (presentation f (restrictChart p W)).ker ≤
      (presentation g W).ker.comap
        (squarePresentationRingHom p g f q hcomm W) :=
  sorry

/-- Scalar tower of the named maps `inverseImageCoeff`, `commInverseImageStructureSheafMap g`,
and their composite, through `g⁻¹𝒪_V(W)`. -/
theorem square_isScalarTower_inverseImage {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    -- Local instance justification (defeq pin): use the scalar action from this square's inverse-image coefficient map at W.
    letI := RingHom.toAlgebra (inverseImageCoeff p g f q hcomm W).hom
    -- Local instance justification (defeq pin): use g's inverse-image algebra at the fixed chart W in the tensor product.
    letI := inverseImageAlgebra g W
    -- Local instance justification (defeq pin): the composite scalar action below is the one specified by the preceding two coefficient maps.
    letI : Algebra
        ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
        ((commStructureSheaf U).obj.obj W) :=
      RingHom.toAlgebra
        (((commInverseImageStructureSheafMap g).hom.app W).hom.comp
          (inverseImageCoeff p g f q hcomm W).hom)
    IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
      ((commInverseImageStructureSheaf g).obj.obj W)
      ((commStructureSheaf U).obj.obj W) :=
  sorry

/-- Scalar tower of the named maps `commInverseImageStructureSheafMap f`, `structureCoeff`,
and the composite `commInverseImageStructureSheafMap g` after `inverseImageCoeff`. -/
theorem square_isScalarTower_structure {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    -- Local instance justification (defeq pin): use f's inverse-image algebra on the restricted chart for this scalar-extension map.
    letI := inverseImageAlgebra f (restrictChart p W)
    -- Local instance justification (defeq pin): the target scalar action is induced by the chart's structure-coefficient homomorphism.
    letI := RingHom.toAlgebra (structureCoeff p W).hom
    -- Local instance justification (defeq pin): use the composite of these two chartwise scalar actions in the tensor construction below.
    letI : Algebra
        ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
        ((commStructureSheaf U).obj.obj W) :=
      RingHom.toAlgebra
        (((commInverseImageStructureSheafMap g).hom.app W).hom.comp
          (inverseImageCoeff p g f q hcomm W).hom)
    IsScalarTower
      ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
      ((commStructureSheaf X).obj.obj (restrictChart p W))
      ((commStructureSheaf U).obj.obj W) :=
  sorry

/-- The polynomial comparison commutes with the canonical presentation maps. -/
theorem squarePresentationHom_toRingHom_algebraMap {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := RingHom.toAlgebra (inverseImageCoeff p g f q hcomm W).hom
  -- Local instance justification (noncanonical choice): structure restriction along `p`.
  letI := RingHom.toAlgebra (structureCoeff p W).hom
  -- Local instance justification (noncanonical choice): composite algebra `f⁻¹𝒪_Y(jW) → 𝒪_U(W)`.
  letI : Algebra
      ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
      ((commStructureSheaf U).obj.obj W) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap g).hom.app W).hom.comp
        (inverseImageCoeff p g f q hcomm W).hom)
  -- Local instance justification (proof-local temporary data): named tower law through `g⁻¹𝒪_V(W)`.
  letI := square_isScalarTower_inverseImage p g f q hcomm W
  -- Local instance justification (proof-local temporary data): named tower law through `𝒪_X(jW)`.
  letI := square_isScalarTower_structure p g f q hcomm W

  ∀ x : (commInverseImageStructureSheaf f).obj.obj (restrictChart p W), squarePresentationRingHom p g f q hcomm W (algebraMap ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)) ((presentation f (restrictChart p W)).toExtension).Ring x) =
      algebraMap ((commInverseImageStructureSheaf g).obj.obj W) ((presentation g W).toExtension).Ring (algebraMap ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)) ((commInverseImageStructureSheaf g).obj.obj W) x) :=
  sorry

/-- The polynomial comparison commutes with the canonical presentation maps. -/
theorem squarePresentationHom_algebraMap_toRingHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := RingHom.toAlgebra (inverseImageCoeff p g f q hcomm W).hom
  -- Local instance justification (noncanonical choice): structure restriction along `p`.
  letI := RingHom.toAlgebra (structureCoeff p W).hom
  -- Local instance justification (noncanonical choice): composite algebra `f⁻¹𝒪_Y(jW) → 𝒪_U(W)`.
  letI : Algebra
      ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
      ((commStructureSheaf U).obj.obj W) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap g).hom.app W).hom.comp
        (inverseImageCoeff p g f q hcomm W).hom)
  -- Local instance justification (proof-local temporary data): named tower law through `g⁻¹𝒪_V(W)`.
  letI := square_isScalarTower_inverseImage p g f q hcomm W
  -- Local instance justification (proof-local temporary data): named tower law through `𝒪_X(jW)`.
  letI := square_isScalarTower_structure p g f q hcomm W

  ∀ x : ((presentation f (restrictChart p W)).toExtension).Ring, algebraMap ((presentation g W).toExtension).Ring ((commStructureSheaf U).obj.obj W) (squarePresentationRingHom p g f q hcomm W x) =
      algebraMap ((commStructureSheaf X).obj.obj (restrictChart p W)) ((commStructureSheaf U).obj.obj W) (algebraMap ((presentation f (restrictChart p W)).toExtension).Ring ((commStructureSheaf X).obj.obj (restrictChart p W)) x) :=
  sorry

/-- The morphism of canonical presentations induced by a commutative étale square. -/
def squarePresentationHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := RingHom.toAlgebra (inverseImageCoeff p g f q hcomm W).hom
  -- Local instance justification (noncanonical choice): structure restriction along `p`.
  letI := RingHom.toAlgebra (structureCoeff p W).hom
  -- Local instance justification (noncanonical choice): composite algebra `f⁻¹𝒪_Y(jW) → 𝒪_U(W)`.
  letI : Algebra
      ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
      ((commStructureSheaf U).obj.obj W) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap g).hom.app W).hom.comp
        (inverseImageCoeff p g f q hcomm W).hom)
  -- Local instance justification (proof-local temporary data): named tower law through `g⁻¹𝒪_V(W)`.
  letI := square_isScalarTower_inverseImage p g f q hcomm W
  -- Local instance justification (proof-local temporary data): named tower law through `𝒪_X(jW)`.
  letI := square_isScalarTower_structure p g f q hcomm W
  ({ toRingHom := squarePresentationRingHom p g f q hcomm W
     toRingHom_algebraMap := squarePresentationHom_toRingHom_algebraMap p g f q hcomm W
     algebraMap_toRingHom := squarePresentationHom_algebraMap_toRingHom p g f q hcomm W } :
    ((presentation f (restrictChart p W)).toExtension).Hom
      ((presentation g W).toExtension))

/-- The conormal comparison respects addition. -/
theorem cotangentObj_squareMap_add {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := (inverseImageCoeff p g f q hcomm W).hom.toAlgebra

  let F : (cotangentObj f (restrictChart p W)) → (cotangentObj g W) := fun x ↦
        Cotangent.of
          (Ideal.mapCotangent (presentation f (restrictChart p W)).ker
            (presentation g W).ker
            (squarePresentationAlgHom p g f q hcomm W)
            (squarePresentationKer_le_comap p g f q hcomm W)
            (Cotangent.val (P := (presentation f (restrictChart p W)).toExtension) x))
  ∀ x y : cotangentObj f (restrictChart p W), F (x + y) = F x + F y :=
  sorry

/-- The conormal comparison respects the structure-sheaf scalar action. -/
theorem cotangentObj_squareMap_smul {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := (inverseImageCoeff p g f q hcomm W).hom.toAlgebra

  let F : (cotangentObj f (restrictChart p W)) → (cotangentObj g W) := fun x ↦
        Cotangent.of
          (Ideal.mapCotangent (presentation f (restrictChart p W)).ker
            (presentation g W).ker
            (squarePresentationAlgHom p g f q hcomm W)
            (squarePresentationKer_le_comap p g f q hcomm W)
            (Cotangent.val (P := (presentation f (restrictChart p W)).toExtension) x))
  ∀ (r : (commStructureSheaf X).obj.obj (restrictChart p W)) (x : cotangentObj f (restrictChart p W)), F (r • x) = (structureCoeff p W).hom r • F x :=
  sorry

/-- Objectwise comparison of conormal terms of a commutative étale square. -/
def cotangentObj_squareMap {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    cotangentObj f (restrictChart p W) ⟶
      (ModuleCat.restrictScalars (structureCoeff p W).hom).obj (cotangentObj g W) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := (inverseImageCoeff p g f q hcomm W).hom.toAlgebra
  ConcreteCategory.ofHom (C := ModuleCat ((commStructureSheaf X).obj.obj (restrictChart p W)))
    { toFun := fun x ↦
        Cotangent.of
          (Ideal.mapCotangent (presentation f (restrictChart p W)).ker
            (presentation g W).ker
            (squarePresentationAlgHom p g f q hcomm W)
            (squarePresentationKer_le_comap p g f q hcomm W)
            (Cotangent.val (P := (presentation f (restrictChart p W)).toExtension) x))
      map_add' := cotangentObj_squareMap_add p g f q hcomm W
      map_smul' := cotangentObj_squareMap_smul p g f q hcomm W }

/-- Objectwise comparison of presentation cotangent-space terms of a commutative étale square. -/
def cotangentSpaceObj_squareMap {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    cotangentSpaceObj f (restrictChart p W) ⟶
      (ModuleCat.restrictScalars (structureCoeff p W).hom).obj
        (cotangentSpaceObj g W) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): coefficient restriction of the square.
  letI := RingHom.toAlgebra (inverseImageCoeff p g f q hcomm W).hom
  -- Local instance justification (noncanonical choice): structure restriction along `p`.
  letI := RingHom.toAlgebra (structureCoeff p W).hom
  -- Local instance justification (noncanonical choice): composite algebra `f⁻¹𝒪_Y(jW) → 𝒪_U(W)`.
  letI : Algebra
      ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
      ((commStructureSheaf U).obj.obj W) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap g).hom.app W).hom.comp
        (inverseImageCoeff p g f q hcomm W).hom)
  -- Local instance justification (proof-local temporary data): named tower law through `g⁻¹𝒪_V(W)`.
  letI := square_isScalarTower_inverseImage p g f q hcomm W
  -- Local instance justification (proof-local temporary data): named tower law through `𝒪_X(jW)`.
  letI := square_isScalarTower_structure p g f q hcomm W
  ConcreteCategory.ofHom (C := ModuleCat ((commStructureSheaf X).obj.obj (restrictChart p W)))
    (CotangentSpace.map (squarePresentationHom p g f q hcomm W))

/-- The sectionwise comparison commutes with presheaf restriction. -/
theorem cotangentPresheaf_squareHom_naturality {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q)
    {W Z : (smallEtaleSite U)ᵒᵖ} (a : W ⟶ Z) :
    ((PresheafOfModules.pushforward (restrictStructureMap p).hom).obj (cotangentPresheaf f)).map a ≫
        (ModuleCat.restrictScalars ((structureSheaf U).obj.map a).hom).map
          (cotangentObj_squareMap p g f q hcomm Z) =
      cotangentObj_squareMap p g f q hcomm W ≫ (cotangentPresheaf g).map a :=
  sorry

/-- Presheaf-level comparison of conormal terms after étale restriction of sites. -/
def cotangentPresheaf_squareHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (PresheafOfModules.pushforward (restrictStructureMap p).hom).obj (cotangentPresheaf f) ⟶
      cotangentPresheaf g where
  app := cotangentObj_squareMap p g f q hcomm
  naturality := fun {_ _} a ↦ cotangentPresheaf_squareHom_naturality p g f q hcomm a

/-- The sectionwise comparison commutes with presheaf restriction. -/
theorem cotangentSpacePresheaf_squareHom_naturality {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q)
    {W Z : (smallEtaleSite U)ᵒᵖ} (a : W ⟶ Z) :
    ((PresheafOfModules.pushforward (restrictStructureMap p).hom).obj (cotangentSpacePresheaf f)).map a ≫
        (ModuleCat.restrictScalars ((structureSheaf U).obj.map a).hom).map
          (cotangentSpaceObj_squareMap p g f q hcomm Z) =
      cotangentSpaceObj_squareMap p g f q hcomm W ≫ (cotangentSpacePresheaf g).map a :=
  sorry

/-- Presheaf-level comparison of presentation cotangent-space terms after étale restriction. -/
def cotangentSpacePresheaf_squareHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (PresheafOfModules.pushforward (restrictStructureMap p).hom).obj
        (cotangentSpacePresheaf f) ⟶
      cotangentSpacePresheaf g where
  app := cotangentSpaceObj_squareMap p g f q hcomm
  naturality := fun {_ _} a ↦ cotangentSpacePresheaf_squareHom_naturality p g f q hcomm a

/-- The reverse polynomial-ring map of canonical presentations of a commutative étale square. -/
def squarePresentationRingHomInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    MvPolynomial ((commStructureSheaf U).obj.obj W)
        ((commInverseImageStructureSheaf g).obj.obj W) →+*
      MvPolynomial ((commStructureSheaf X).obj.obj (restrictChart p W))
        ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)) :=
  (MvPolynomial.rename fun s ↦ (structureCoeffInv p W).hom s).toRingHom.comp
    (MvPolynomial.map (inverseImageCoeffInv p g f q hcomm W).hom)

/-- The polynomial comparison preserves the specified coefficient action. -/
theorem squarePresentationAlgHomInv_commutes {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := (inverseImageCoeffInv p g f q hcomm W).hom.toAlgebra

  ∀ r : (commInverseImageStructureSheaf g).obj.obj W,
    squarePresentationRingHomInv p g f q hcomm W (algebraMap ((commInverseImageStructureSheaf g).obj.obj W) (MvPolynomial ((commStructureSheaf U).obj.obj W) ((commInverseImageStructureSheaf g).obj.obj W)) r) =
      algebraMap ((commInverseImageStructureSheaf g).obj.obj W) (MvPolynomial ((commStructureSheaf X).obj.obj (restrictChart p W)) ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))) r :=
  sorry

/-- The reverse algebra homomorphism of canonical presentations of a commutative étale square. -/
def squarePresentationAlgHomInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :=
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := (inverseImageCoeffInv p g f q hcomm W).hom.toAlgebra
  ({ squarePresentationRingHomInv p g f q hcomm W with
      commutes' := squarePresentationAlgHomInv_commutes p g f q hcomm W } :
    MvPolynomial ((commStructureSheaf U).obj.obj W)
        ((commInverseImageStructureSheaf g).obj.obj W) →ₐ[
      (commInverseImageStructureSheaf g).obj.obj W]
      MvPolynomial ((commStructureSheaf X).obj.obj (restrictChart p W))
        ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)))

/-- Reverse scalar tower of the named maps `inverseImageCoeffInv`,
`commInverseImageStructureSheafMap f`, and their composite. -/
theorem square_isScalarTower_inverseImage_inv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    -- Local instance justification (defeq pin): use the inverse coefficient homomorphism's scalar action for this inverse comparison.
    letI := RingHom.toAlgebra (inverseImageCoeffInv p g f q hcomm W).hom
    -- Local instance justification (defeq pin): use f's inverse-image algebra at the restricted chart in the inverse tensor map.
    letI := inverseImageAlgebra f (restrictChart p W)
    -- Local instance justification (defeq pin): compose these fixed chartwise actions to match the source algebra of the inverse map.
    letI : Algebra
        ((commInverseImageStructureSheaf g).obj.obj W)
        ((commStructureSheaf X).obj.obj (restrictChart p W)) :=
      RingHom.toAlgebra
        (((commInverseImageStructureSheafMap f).hom.app (restrictChart p W)).hom.comp
          (inverseImageCoeffInv p g f q hcomm W).hom)
    IsScalarTower
      ((commInverseImageStructureSheaf g).obj.obj W)
      ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W))
      ((commStructureSheaf X).obj.obj (restrictChart p W)) :=
  sorry

/-- The reverse kernel comparison of canonical presentations of a commutative étale square. -/
theorem squarePresentationKer_le_comap_inv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
    letI := inverseImageAlgebra g W
    -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
    letI := inverseImageAlgebra f (restrictChart p W)
    (presentation g W).ker ≤
      (presentation f (restrictChart p W)).ker.comap
        (squarePresentationRingHomInv p g f q hcomm W) :=
  sorry

/-- The conormal comparison respects addition. -/
theorem cotangentObj_squareMapInv_add {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := (inverseImageCoeffInv p g f q hcomm W).hom.toAlgebra

  let F : (cotangentObj g W) → (cotangentObj f (restrictChart p W)) := fun x ↦
        Cotangent.of
          (Ideal.mapCotangent (presentation g W).ker
            (presentation f (restrictChart p W)).ker
            (squarePresentationAlgHomInv p g f q hcomm W)
            (squarePresentationKer_le_comap_inv p g f q hcomm W)
            (Cotangent.val (P := (presentation g W).toExtension) x))
  ∀ x y : cotangentObj g W, F (x + y) = F x + F y :=
  sorry

/-- The conormal comparison respects the structure-sheaf scalar action. -/
theorem cotangentObj_squareMapInv_smul {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := (inverseImageCoeffInv p g f q hcomm W).hom.toAlgebra

  let F : (cotangentObj g W) → (cotangentObj f (restrictChart p W)) := fun x ↦
        Cotangent.of
          (Ideal.mapCotangent (presentation g W).ker
            (presentation f (restrictChart p W)).ker
            (squarePresentationAlgHomInv p g f q hcomm W)
            (squarePresentationKer_le_comap_inv p g f q hcomm W)
            (Cotangent.val (P := (presentation g W).toExtension) x))
  ∀ (r : (commStructureSheaf U).obj.obj W) (x : cotangentObj g W), F (r • x) = (structureCoeffInv p W).hom r • F x :=
  sorry

/-- Reverse objectwise comparison of conormal terms of a commutative étale square. -/
def cotangentObj_squareMapInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    cotangentObj g W ⟶
      (ModuleCat.restrictScalars (structureCoeffInv p W).hom).obj
        (cotangentObj f (restrictChart p W)) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := (inverseImageCoeffInv p g f q hcomm W).hom.toAlgebra
  ConcreteCategory.ofHom (C := ModuleCat ((commStructureSheaf U).obj.obj W))
    { toFun := fun x ↦
        Cotangent.of
          (Ideal.mapCotangent (presentation g W).ker
            (presentation f (restrictChart p W)).ker
            (squarePresentationAlgHomInv p g f q hcomm W)
            (squarePresentationKer_le_comap_inv p g f q hcomm W)
            (Cotangent.val (P := (presentation g W).toExtension) x))
      map_add' := cotangentObj_squareMapInv_add p g f q hcomm W
      map_smul' := cotangentObj_squareMapInv_smul p g f q hcomm W }

/-- The polynomial comparison commutes with the canonical presentation maps. -/
theorem squarePresentationHomInv_toRingHom_algebraMap {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := RingHom.toAlgebra (inverseImageCoeffInv p g f q hcomm W).hom
  -- Local instance justification (noncanonical choice): reverse structure restriction along `p`.
  letI := RingHom.toAlgebra (structureCoeffInv p W).hom
  -- Local instance justification (noncanonical choice): composite algebra `g⁻¹𝒪_V(W) → 𝒪_X(jW)`.
  letI : Algebra
      ((commInverseImageStructureSheaf g).obj.obj W)
      ((commStructureSheaf X).obj.obj (restrictChart p W)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app (restrictChart p W)).hom.comp
        (inverseImageCoeffInv p g f q hcomm W).hom)
  -- Local instance justification (proof-local temporary data): reverse tower through `f⁻¹𝒪_Y(jW)`.
  letI := square_isScalarTower_inverseImage_inv p g f q hcomm W

  ∀ x : (commInverseImageStructureSheaf g).obj.obj W, squarePresentationRingHomInv p g f q hcomm W (algebraMap ((commInverseImageStructureSheaf g).obj.obj W) ((presentation g W).toExtension).Ring x) =
      algebraMap ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)) ((presentation f (restrictChart p W)).toExtension).Ring (algebraMap ((commInverseImageStructureSheaf g).obj.obj W) ((commInverseImageStructureSheaf f).obj.obj (restrictChart p W)) x) :=
  sorry

/-- The polynomial comparison commutes with the canonical presentation maps. -/
theorem squarePresentationHomInv_algebraMap_toRingHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := RingHom.toAlgebra (inverseImageCoeffInv p g f q hcomm W).hom
  -- Local instance justification (noncanonical choice): reverse structure restriction along `p`.
  letI := RingHom.toAlgebra (structureCoeffInv p W).hom
  -- Local instance justification (noncanonical choice): composite algebra `g⁻¹𝒪_V(W) → 𝒪_X(jW)`.
  letI : Algebra
      ((commInverseImageStructureSheaf g).obj.obj W)
      ((commStructureSheaf X).obj.obj (restrictChart p W)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app (restrictChart p W)).hom.comp
        (inverseImageCoeffInv p g f q hcomm W).hom)
  -- Local instance justification (proof-local temporary data): reverse tower through `f⁻¹𝒪_Y(jW)`.
  letI := square_isScalarTower_inverseImage_inv p g f q hcomm W

  ∀ x : ((presentation g W).toExtension).Ring, algebraMap ((presentation f (restrictChart p W)).toExtension).Ring ((commStructureSheaf X).obj.obj (restrictChart p W)) (squarePresentationRingHomInv p g f q hcomm W x) =
      algebraMap ((commStructureSheaf U).obj.obj W) ((commStructureSheaf X).obj.obj (restrictChart p W)) (algebraMap ((presentation g W).toExtension).Ring ((commStructureSheaf U).obj.obj W) x) :=
  sorry

/-- The reverse morphism of canonical presentations of a commutative étale square. -/
def squarePresentationHomInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := RingHom.toAlgebra (inverseImageCoeffInv p g f q hcomm W).hom
  -- Local instance justification (noncanonical choice): reverse structure restriction along `p`.
  letI := RingHom.toAlgebra (structureCoeffInv p W).hom
  -- Local instance justification (noncanonical choice): composite algebra `g⁻¹𝒪_V(W) → 𝒪_X(jW)`.
  letI : Algebra
      ((commInverseImageStructureSheaf g).obj.obj W)
      ((commStructureSheaf X).obj.obj (restrictChart p W)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app (restrictChart p W)).hom.comp
        (inverseImageCoeffInv p g f q hcomm W).hom)
  -- Local instance justification (proof-local temporary data): reverse tower through `f⁻¹𝒪_Y(jW)`.
  letI := square_isScalarTower_inverseImage_inv p g f q hcomm W
  ({ toRingHom := squarePresentationRingHomInv p g f q hcomm W
     toRingHom_algebraMap := squarePresentationHomInv_toRingHom_algebraMap p g f q hcomm W
     algebraMap_toRingHom := squarePresentationHomInv_algebraMap_toRingHom p g f q hcomm W } :
    ((presentation g W).toExtension).Hom
      ((presentation f (restrictChart p W)).toExtension))

/-- Reverse objectwise comparison of presentation cotangent-space terms. -/
def cotangentSpaceObj_squareMapInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (W : (smallEtaleSite U)ᵒᵖ) :
    cotangentSpaceObj g W ⟶
      (ModuleCat.restrictScalars (structureCoeffInv p W).hom).obj
        (cotangentSpaceObj f (restrictChart p W)) :=
  -- Local instance justification (noncanonical choice): objectwise algebra of `g^♯` at `W`.
  letI := inverseImageAlgebra g W
  -- Local instance justification (noncanonical choice): objectwise algebra of `f^♯` at `jW`.
  letI := inverseImageAlgebra f (restrictChart p W)
  -- Local instance justification (noncanonical choice): reverse coefficient restriction.
  letI := RingHom.toAlgebra (inverseImageCoeffInv p g f q hcomm W).hom
  -- Local instance justification (noncanonical choice): reverse structure restriction along `p`.
  letI := RingHom.toAlgebra (structureCoeffInv p W).hom
  -- Local instance justification (noncanonical choice): composite algebra `g⁻¹𝒪_V(W) → 𝒪_X(jW)`.
  letI : Algebra
      ((commInverseImageStructureSheaf g).obj.obj W)
      ((commStructureSheaf X).obj.obj (restrictChart p W)) :=
    RingHom.toAlgebra
      (((commInverseImageStructureSheafMap f).hom.app (restrictChart p W)).hom.comp
        (inverseImageCoeffInv p g f q hcomm W).hom)
  -- Local instance justification (proof-local temporary data): reverse tower through `f⁻¹𝒪_Y(jW)`.
  letI := square_isScalarTower_inverseImage_inv p g f q hcomm W
  ConcreteCategory.ofHom (C := ModuleCat ((commStructureSheaf U).obj.obj W))
    (CotangentSpace.map (squarePresentationHomInv p g f q hcomm W))

/-- The sectionwise comparison commutes with presheaf restriction. -/
theorem cotangentPresheaf_squareHomInv_naturality {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q)
    {W Z : (smallEtaleSite U)ᵒᵖ} (a : W ⟶ Z) :
    (cotangentPresheaf g).map a ≫
        (ModuleCat.restrictScalars ((structureSheaf U).obj.map a).hom).map
          (cotangentObj_squareMapInv p g f q hcomm Z) =
      cotangentObj_squareMapInv p g f q hcomm W ≫ ((PresheafOfModules.pushforward (restrictStructureMap p).hom).obj (cotangentPresheaf f)).map a :=
  sorry

/-- Reverse presheaf-level comparison of conormal terms after étale restriction of sites. -/
def cotangentPresheaf_squareHomInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    cotangentPresheaf g ⟶
      (PresheafOfModules.pushforward (restrictStructureMap p).hom).obj (cotangentPresheaf f) where
  app := cotangentObj_squareMapInv p g f q hcomm
  naturality := fun {_ _} a ↦ cotangentPresheaf_squareHomInv_naturality p g f q hcomm a

/-- The sectionwise comparison commutes with presheaf restriction. -/
theorem cotangentSpacePresheaf_squareHomInv_naturality {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q)
    {W Z : (smallEtaleSite U)ᵒᵖ} (a : W ⟶ Z) :
    (cotangentSpacePresheaf g).map a ≫
        (ModuleCat.restrictScalars ((structureSheaf U).obj.map a).hom).map
          (cotangentSpaceObj_squareMapInv p g f q hcomm Z) =
      cotangentSpaceObj_squareMapInv p g f q hcomm W ≫ ((PresheafOfModules.pushforward (restrictStructureMap p).hom).obj (cotangentSpacePresheaf f)).map a :=
  sorry

/-- Reverse presheaf-level comparison of presentation cotangent-space terms. -/
def cotangentSpacePresheaf_squareHomInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    cotangentSpacePresheaf g ⟶
      (PresheafOfModules.pushforward (restrictStructureMap p).hom).obj
        (cotangentSpacePresheaf f) where
  app := cotangentSpaceObj_squareMapInv p g f q hcomm
  naturality := fun {_ _} a ↦ cotangentSpacePresheaf_squareHomInv_naturality p g f q hcomm a

/-- Degree `-1` component of étale restriction of naive cotangent complexes. -/
def etaleRestrictHom_negOne {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (restrictFunctor p).obj (cotangentSheaf f) ⟶ cotangentSheaf g :=
  restrictSheafificationInv p (cotangentPresheaf f) ≫
    (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).map
      (cotangentPresheaf_squareHom p g f q hcomm)

/-- Degree `0` component of étale restriction of naive cotangent complexes. -/
def etaleRestrictHom_zero {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (restrictFunctor p).obj (cotangentSpaceSheaf f) ⟶ cotangentSpaceSheaf g :=
  restrictSheafificationInv p (cotangentSpacePresheaf f) ≫
    (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).map
      (cotangentSpacePresheaf_squareHom p g f q hcomm)

/-- Degreewise components of the étale-restriction comparison of naive cotangent complexes. -/
def etaleRestrictHom_app {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (n : ℤ) :
    (((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f)).X n ⟶
      (naiveCotangent g).X n :=
  match n with
  | Int.negSucc 0 => etaleRestrictHom_negOne p g f q hcomm
  | Int.ofNat 0 => etaleRestrictHom_zero p g f q hcomm
  | _ => 0

/-- The degreewise comparison maps commute with differentials. -/
theorem etaleRestrictHom_app_comm {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    etaleRestrictHom_app p g f q hcomm i ≫ (naiveCotangent g).d i j =
      (((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f)).d i j ≫
        etaleRestrictHom_app p g f q hcomm j :=
  sorry

/-- The canonical comparison `((NL_f)|_{U_étale}) ⟶ NL_g` of complexes of `𝒪_U`-modules. -/
def etaleRestrictHom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    ((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f) ⟶
      naiveCotangent g where
  f n := etaleRestrictHom_app p g f q hcomm n
  comm' i j hij := etaleRestrictHom_app_comm p g f q hcomm i j hij

/-- The degree `-1` component of `etaleRestrictHom` is the conormal comparison. -/
theorem etaleRestrictHom_f_negOne {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (etaleRestrictHom p g f q hcomm).f (-1) =
      etaleRestrictHom_negOne p g f q hcomm :=
  sorry

/-- The degree `0` component of `etaleRestrictHom` is the presentation-differentials comparison. -/
theorem etaleRestrictHom_f_zero {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (etaleRestrictHom p g f q hcomm).f 0 =
      etaleRestrictHom_zero p g f q hcomm :=
  sorry

/-- Degree `-1` component of the reverse étale restriction of naive cotangent complexes. -/
def etaleRestrictHomInv_negOne {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    cotangentSheaf g ⟶ (restrictFunctor p).obj (cotangentSheaf f) :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).map
      (cotangentPresheaf_squareHomInv p g f q hcomm) ≫
    restrictSheafificationHom p (cotangentPresheaf f)

/-- Degree `0` component of the reverse étale restriction of naive cotangent complexes. -/
def etaleRestrictHomInv_zero {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    cotangentSpaceSheaf g ⟶ (restrictFunctor p).obj (cotangentSpaceSheaf f) :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf U).obj)).map
      (cotangentSpacePresheaf_squareHomInv p g f q hcomm) ≫
    restrictSheafificationHom p (cotangentSpacePresheaf f)

/-- Degreewise components of the reverse étale-restriction comparison. -/
def etaleRestrictHomInv_app {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (n : ℤ) :
    (naiveCotangent g).X n ⟶
      (((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f)).X n :=
  match n with
  | Int.negSucc 0 => etaleRestrictHomInv_negOne p g f q hcomm
  | Int.ofNat 0 => etaleRestrictHomInv_zero p g f q hcomm
  | _ => 0

/-- The reverse degreewise comparison maps commute with differentials. -/
theorem etaleRestrictHomInv_app_comm {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    etaleRestrictHomInv_app p g f q hcomm i ≫
        (((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f)).d i j =
      (naiveCotangent g).d i j ≫ etaleRestrictHomInv_app p g f q hcomm j :=
  sorry

/-- The reverse comparison `NL_g ⟶ ((NL_f)|_{U_étale})` of complexes of `𝒪_U`-modules. -/
def etaleRestrictHomInv {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    naiveCotangent g ⟶
      ((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f) where
  f n := etaleRestrictHomInv_app p g f q hcomm n
  comm' i j hij := etaleRestrictHomInv_app_comm p g f q hcomm i j hij

/-- The explicit étale comparison chain maps compose to the identity. -/
theorem etaleRestrictIso_hom_inv_id {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    etaleRestrictHom p g f q hcomm ≫ etaleRestrictHomInv p g f q hcomm = 𝟙 _ :=
  sorry

/-- The explicit étale comparison chain maps compose to the identity. -/
theorem etaleRestrictIso_inv_hom_id {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    etaleRestrictHomInv p g f q hcomm ≫ etaleRestrictHom p g f q hcomm = 𝟙 _ :=
  sorry

/-- The canonical isomorphism `(NL_f)|_{U_étale} ≅ NL_g` of complexes of `𝒪_U`-modules. -/
def etaleRestrictIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    ((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f) ≅
      naiveCotangent g where
  hom := etaleRestrictHom p g f q hcomm
  inv := etaleRestrictHomInv p g f q hcomm
  hom_inv_id := etaleRestrictIso_hom_inv_id p g f q hcomm
  inv_hom_id := etaleRestrictIso_inv_hom_id p g f q hcomm

/-- The reverse comparison of étale restriction of naive cotangent complexes is an isomorphism. -/
instance etaleRestrictHomInv_isIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    IsIso (etaleRestrictHomInv p g f q hcomm) :=
  (etaleRestrictIso p g f q hcomm).isIso_inv

/-- Étale restriction of naive cotangent complexes is an isomorphism of complexes. -/
instance etaleRestrictHom_isIso {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    IsIso (etaleRestrictHom p g f q hcomm) :=
  (etaleRestrictIso p g f q hcomm).isIso_hom

/-- The derived identification `NL_{X/Y}|_{U_étale} ≅ NL_{U/V}` in `D(𝒪_U)`. -/
def etaleRestrictIso_derived {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    DerivedCategory.Q.obj
        (((restrictFunctor p).mapHomologicalComplex (up ℤ)).obj (naiveCotangent f)) ≅
      DerivedCategory.Q.obj (naiveCotangent g) :=
  DerivedCategory.Q.mapIso (etaleRestrictIso p g f q hcomm)

/-- The derived identification is the image of `etaleRestrictIso` under `DerivedCategory.Q`. -/
theorem etaleRestrictIso_derived_hom {U V X Y : AlgebraicSpace S}
    (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y) [Etale p] [Etale q]
    (hcomm : p ≫ f = g ≫ q) :
    (etaleRestrictIso_derived p g f q hcomm).hom =
      DerivedCategory.Q.map (etaleRestrictHom p g f q hcomm) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
