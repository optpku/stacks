/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap87.Lemma_87_19_13_Over
public import stacks_project.Chap87.Lemma_87_34_6_Comparison

/-!
# Comparison of affine étale slices of an affine formal algebraic space

The affine étale site of the reduction of an affine formal algebraic space `X`
is compared with the category of morphisms `φ : U ⟶ X` of affine formal
algebraic spaces that are representable by algebraic spaces and étale. The
forward functor sends `φ` to a representing affine scheme of the fibre
product `U ×_X X_red`. The inverse sends an affine scheme étale over `X_red`
to the extension `U_{V,ψ}` of Lemma 87.34.6, upgraded by a directed affine
thickening presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MorphismProperty CategoryTheory.ObjectProperty Opposite
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}
variable {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] [Reduction X]

/-- The domain of an affine étale slice object is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_affineEtaleOver (U : AffineEtaleOver X) :
    IsFormalAlgebraicSpace U.obj.left :=
  sorry

/-- The identity functor does not change the domain of an affine étale slice
object. -/
instance instIsFormalAlgebraicSpace_id_obj_affineEtaleOver
    (U : AffineEtaleOver X) :
    IsFormalAlgebraicSpace ((𝟭 ((Over S)ᵒᵖ ⥤ Type u)).obj U.obj.left) :=
  inferInstanceAs (IsFormalAlgebraicSpace U.obj.left)

/-- The codomain of an affine étale slice object is the standing formal
algebraic space `X`. -/
instance instIsFormalAlgebraicSpace_fromPUnit_obj_affineEtaleOver
    (U : AffineEtaleOver X) :
    IsFormalAlgebraicSpace ((Functor.fromPUnit X).obj U.obj.right) :=
  inferInstanceAs (IsFormalAlgebraicSpace X)

/-- The reduction of the standing formal algebraic space `X` is inherited by
the comma codomain of an affine étale slice object. -/
instance instReduction_fromPUnit_obj_affineEtaleOver (U : AffineEtaleOver X) :
    Reduction ((Functor.fromPUnit X).obj U.obj.right) :=
  inferInstanceAs (Reduction X)

/-- Affine formal domains in the étale slice are in particular formal algebraic
spaces. -/
theorem isAffineFormalDomain_le_isFormalDomain :
    isAffineFormalDomain X ≤ isFormalDomain X :=
  sorry

/-- The forgetful functor from affine étale morphisms into `X` to étale
morphisms of formal algebraic spaces into `X`. -/
def affineEtaleOverForget : AffineEtaleOver X ⥤ EtaleOver X :=
  ιOfLE isAffineFormalDomain_le_isFormalDomain

/-- On objects, `affineEtaleOverForget` retains the underlying étale slice
object. -/
@[simp]
theorem affineEtaleOverForget_obj (U : AffineEtaleOver X) :
    (affineEtaleOverForget.obj U).obj = U.obj :=
  rfl

/-- The inclusion of affine schemes étale over `X_red` into algebraic spaces
étale over `X_red`. -/
def affineSpacesInclusion :
    AlgebraicSpace.affineEtaleSite (reduction X) ⥤
      AlgebraicSpace.spacesEtaleSite (reduction X) :=
  AlgebraicSpace.affineEtaleInclusion (reduction X) ⋙
    AlgebraicSpace.smallEtaleInclusion (reduction X)

/-- On objects, `affineSpacesInclusion` is the composite of the affine and
small étale inclusions. -/
@[simp]
theorem affineSpacesInclusion_obj
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    affineSpacesInclusion.obj V =
      (AlgebraicSpace.affineEtaleInclusion (reduction X) ⋙
        AlgebraicSpace.smallEtaleInclusion (reduction X)).obj V :=
  rfl

/-- The structural morphism of `affineSpacesInclusion.obj V` is the structural
morphism of `V`. -/
@[simp]
theorem affineSpacesInclusion_obj_hom
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    (affineSpacesInclusion.obj V).hom = V.obj.hom :=
  rfl

/-- The underlying algebraic space of `affineSpacesInclusion.obj V` is the
scheme of `V`, viewed as an algebraic space. -/
@[simp]
theorem affineSpacesInclusion_obj_left
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    (affineSpacesInclusion.obj V).left = AlgebraicSpace.ofOver V.obj.left :=
  rfl

/-- The reduction of an affine formal algebraic space is an affine algebraic
space. -/
theorem isAffine_reduction
    (hX :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X) :
    AlgebraicSpace.IsAffine (reduction X) :=
  sorry

/-- The fibre product `U ×_X X_red` is a representable functor on schemes over
`S`, when `U ⟶ X` is an affine étale morphism of affine formal algebraic
spaces. -/
instance instIsRepresentable_pullback_reductionι (U : AffineEtaleOver X) :
    (pullback (reductionι X) U.obj.hom).IsRepresentable :=
  sorry

/-- A representing affine scheme of the fibre product `U ×_X X_red`. -/
def fibreAffineScheme (U : AffineEtaleOver X) : Over S :=
  (pullback (reductionι X) U.obj.hom).reprX

/-- `fibreAffineScheme U` is the Yoneda representing object of
`U ×_X X_red`. -/
@[simp]
theorem fibreAffineScheme_def (U : AffineEtaleOver X) :
    fibreAffineScheme U = (pullback (reductionι X) U.obj.hom).reprX :=
  rfl

/-- The Yoneda embedding of `fibreAffineScheme U` recovers the fibre product
functor `U ×_X X_red`. -/
def fibreAffineSchemeIso (U : AffineEtaleOver X) :
    yoneda.obj (fibreAffineScheme U) ≅ pullback (reductionι X) U.obj.hom :=
  (pullback (reductionι X) U.obj.hom).reprW

/-- The forward map of `fibreAffineSchemeIso U` is the representing Yoneda
isomorphism. -/
@[simp]
theorem fibreAffineSchemeIso_hom (U : AffineEtaleOver X) :
    (fibreAffineSchemeIso U).hom = (pullback (reductionι X) U.obj.hom).reprW.hom :=
  rfl

/-- Any other representing scheme of `U ×_X X_red` is isomorphic to
`fibreAffineScheme U`. -/
theorem fibreAffineScheme_unique (U : AffineEtaleOver X) {T : Over S}
    (e : yoneda.obj T ≅ pullback (reductionι X) U.obj.hom) :
    Nonempty (T ≅ fibreAffineScheme U) :=
  ⟨CategoryTheory.Yoneda.fullyFaithful.preimageIso
    (e ≪≫ (fibreAffineSchemeIso U).symm)⟩

/-- The representing scheme of `U ×_X X_red` is affine. -/
instance instIsAffine_fibreAffineScheme (U : AffineEtaleOver X) :
    IsAffine (fibreAffineScheme U).left :=
  sorry

/-- The algebraic space associated to `fibreAffineScheme U` is identified with
the fibre product algebraic space `U ×_X X_red`. -/
def fibreToReductionAlong (U : AffineEtaleOver X) :
    AlgebraicSpace.ofOver (fibreAffineScheme U) ≅
      (toSpacesEtale.obj (affineEtaleOverForget.obj U)).left where
  hom :=
    ((fibreAffineSchemeIso U).hom :
      (AlgebraicSpace.ofOver (fibreAffineScheme U)).functorOfPoints ⟶
        (toSpacesEtale.obj (affineEtaleOverForget.obj U)).left.functorOfPoints)
  inv :=
    ((fibreAffineSchemeIso U).inv :
      (toSpacesEtale.obj (affineEtaleOverForget.obj U)).left.functorOfPoints ⟶
        (AlgebraicSpace.ofOver (fibreAffineScheme U)).functorOfPoints)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `fibreToReductionAlong U` is the Yoneda representing
isomorphism of `U ×_X X_red`. -/
theorem fibreToReductionAlong_hom (U : AffineEtaleOver X) :
    (fibreToReductionAlong U).hom = (fibreAffineSchemeIso U).hom :=
  sorry

/-- The structure morphism of the representing affine scheme of `U ×_X X_red`
over `X_red`. -/
def fibreAffineSchemeHom (U : AffineEtaleOver X) :
    AlgebraicSpace.ofOver (fibreAffineScheme U) ⟶ reduction X :=
  (fibreToReductionAlong U).hom ≫
    reductionMap (affineEtaleOverForget.obj U).obj.hom

/-- `fibreAffineSchemeHom U` is the composite of the representing isomorphism
with the projection `U ×_X X_red ⟶ X_red`. -/
theorem fibreAffineSchemeHom_def (U : AffineEtaleOver X) :
    fibreAffineSchemeHom U =
      (fibreToReductionAlong U).hom ≫
        reductionMap (affineEtaleOverForget.obj U).obj.hom :=
  rfl

/-- The structure morphism of `fibreAffineScheme U` over `X_red` is étale. -/
instance instEtale_fibreAffineSchemeHom (U : AffineEtaleOver X) :
    AlgebraicSpace.Etale (fibreAffineSchemeHom U) :=
  sorry

/-- An affine étale slice morphism over `X` is a morphism of domains over `X`. -/
theorem toAffineEtale_map_w {U V : AffineEtaleOver X} (f : U ⟶ V) :
    U.obj.hom ≫ 𝟙 X = f.hom.left ≫ V.obj.hom :=
  sorry

/-- The induced map of representing affine schemes of fibre products along a
morphism of affine étale slice objects. -/
def fibreAffineSchemeMap {U V : AffineEtaleOver X} (f : U ⟶ V) :
    fibreAffineScheme U ⟶ fibreAffineScheme V :=
  CategoryTheory.Yoneda.fullyFaithful.preimage
    ((fibreAffineSchemeIso U).hom ≫
      pullback.map (reductionι X) U.obj.hom (reductionι X) V.obj.hom
        (𝟙 _) f.hom.left (𝟙 _) reductionι_id_comp (toAffineEtale_map_w f) ≫
      (fibreAffineSchemeIso V).inv)

/-- `fibreAffineSchemeMap f` lies over `S`. -/
theorem fibreAffineSchemeMap_w {U V : AffineEtaleOver X} (f : U ⟶ V) :
    (fibreAffineSchemeMap f).left ≫ (fibreAffineScheme V).hom =
      (fibreAffineScheme U).hom :=
  sorry

/-- The induced map of representing affine schemes lies over `X_red`. -/
theorem toAffineEtale_homMk_w {U V : AffineEtaleOver X} (f : U ⟶ V) :
    AlgebraicSpace.ofOverMap (fibreAffineSchemeMap f) ≫ fibreAffineSchemeHom V =
      fibreAffineSchemeHom U :=
  sorry

/-- The forward functor sending an affine étale morphism `φ : U ⟶ X` to a
representing affine scheme of `U ×_X X_red`. -/
def toAffineEtale :
    AffineEtaleOver X ⥤ AlgebraicSpace.affineEtaleSite (reduction X) where
  obj U := AlgebraicSpace.affineEtaleSite.mk (fibreAffineSchemeHom U)
  map {U V} f :=
    homMk
      (MorphismProperty.CostructuredArrow.homMk (fibreAffineSchemeMap f) trivial
        (toAffineEtale_homMk_w f))
  map_id := sorry
  map_comp := sorry

/-- On objects, `toAffineEtale` is `affineEtaleSite.mk` of
`fibreAffineSchemeHom`. -/
@[simp]
theorem toAffineEtale_obj (U : AffineEtaleOver X) :
    toAffineEtale.obj U = AlgebraicSpace.affineEtaleSite.mk (fibreAffineSchemeHom U) :=
  rfl

/-- The underlying scheme over `S` of `toAffineEtale.obj U` is
`fibreAffineScheme U`. -/
@[simp]
theorem toAffineEtale_obj_left (U : AffineEtaleOver X) :
    (toAffineEtale.obj U).obj.left = fibreAffineScheme U :=
  rfl

/-- The structural morphism of `toAffineEtale.obj U` is
`fibreAffineSchemeHom U`. -/
@[simp]
theorem toAffineEtale_obj_hom (U : AffineEtaleOver X) :
    (toAffineEtale.obj U).obj.hom = fibreAffineSchemeHom U :=
  rfl

/-- Comparison of the two incarnations of `U ×_X X_red`: as an algebraic space
via `toSpacesEtale`, and as an affine scheme via `toAffineEtale`. -/
def toSpacesIsoToAffine (U : AffineEtaleOver X) :
    (toSpacesEtale.obj (affineEtaleOverForget.obj U) :
        AlgebraicSpace.spacesEtaleSite (reduction X)) ≅
      (affineSpacesInclusion.obj (toAffineEtale.obj U) :
        AlgebraicSpace.spacesEtaleSite (reduction X)) where
  hom :=
    (MorphismProperty.Over.homMk (fibreToReductionAlong U).inv sorry trivial :
      toSpacesEtale.obj (affineEtaleOverForget.obj U) ⟶
        affineSpacesInclusion.obj (toAffineEtale.obj U))
  inv :=
    (MorphismProperty.Over.homMk (fibreToReductionAlong U).hom sorry trivial :
      affineSpacesInclusion.obj (toAffineEtale.obj U) ⟶
        toSpacesEtale.obj (affineEtaleOverForget.obj U))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying algebraic-space isomorphism of `toSpacesIsoToAffine U` is
the inverse of `fibreToReductionAlong U`. -/
theorem toSpacesIsoToAffine_left (U : AffineEtaleOver X) :
    (toSpacesIsoToAffine U).hom.left = (fibreToReductionAlong U).inv :=
  sorry

/-- The forgetful square relating Lemma 87.34.4 to Lemma 87.34.6 on the
forward functors. -/
def affineEtaleOverForget_comp_toSpacesEtale :
    affineEtaleOverForget ⋙
        (toSpacesEtale : EtaleOver X ⥤ AlgebraicSpace.spacesEtaleSite (reduction X)) ≅
      toAffineEtale ⋙ affineSpacesInclusion :=
  NatIso.ofComponents (fun U ↦ toSpacesIsoToAffine U) sorry

/-- The extension of an affine scheme étale over `X_red` along `X_red ⟶ X`
admits a `Type u` directed affine thickening presentation. -/
theorem exists_isDirectedAffineThickeningColimit_ofAffineEtale
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D
        (extensionAlong (affineSpacesInclusion.obj V)) :=
  sorry

/-- The quasi-inverse sending an affine scheme étale over `X_red` to the
extension `U_{V,ψ} ⟶ X`, as an affine formal algebraic space. -/
def ofAffineEtale :
    AlgebraicSpace.affineEtaleSite (reduction X) ⥤ AffineEtaleOver X where
  obj V :=
    AffineEtaleOver.mk (extensionHom (affineSpacesInclusion.obj V))
      (exists_isDirectedAffineThickeningColimit_ofAffineEtale V)
  map f :=
    ⟨MorphismProperty.Over.homMk
      (extensionAlongMap (affineSpacesInclusion.map f)) sorry trivial⟩
  map_id := sorry
  map_comp := sorry

/-- On objects, `ofAffineEtale` is `AffineEtaleOver.mk` of `extensionHom` of the
included spaces-étale object. -/
theorem ofAffineEtale_obj (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    ofAffineEtale.obj V =
      AffineEtaleOver.mk (extensionHom (affineSpacesInclusion.obj V))
        (exists_isDirectedAffineThickeningColimit_ofAffineEtale V) :=
  rfl

/-- The domain of `ofAffineEtale.obj V` is the extension along `X_red ⟶ X`. -/
@[simp]
theorem ofAffineEtale_obj_left
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    (ofAffineEtale.obj V).obj.left = extensionAlong (affineSpacesInclusion.obj V) :=
  sorry

/-- The structural morphism of `ofAffineEtale.obj V` is `extensionHom` of the
included spaces-étale object. -/
@[simp]
theorem ofAffineEtale_obj_hom
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    (ofAffineEtale.obj V).obj.hom = extensionHom (affineSpacesInclusion.obj V) :=
  sorry

/-- Forgetting affinity on `ofAffineEtale.obj V` recovers `ofSpacesEtale` of the
included spaces-étale object. -/
def ofAffineEtaleIsoOfSpacesEtale
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    affineEtaleOverForget.obj (ofAffineEtale.obj V) ≅
      ofSpacesEtale.obj (affineSpacesInclusion.obj V) where
  hom :=
    (_root_.CategoryTheory.ObjectProperty.homMk (𝟙 (ofAffineEtale.obj V).obj) :
      affineEtaleOverForget.obj (ofAffineEtale.obj V) ⟶
        ofSpacesEtale.obj (affineSpacesInclusion.obj V))
  inv :=
    (_root_.CategoryTheory.ObjectProperty.homMk (𝟙 (ofAffineEtale.obj V).obj) :
      ofSpacesEtale.obj (affineSpacesInclusion.obj V) ⟶
        affineEtaleOverForget.obj (ofAffineEtale.obj V))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forgetful square relating Lemma 87.34.4 to Lemma 87.34.6 on the inverse
functors. -/
def ofAffineEtale_comp_forget :
    ofAffineEtale ⋙ affineEtaleOverForget ≅
      affineSpacesInclusion ⋙
        (ofSpacesEtale :
          AlgebraicSpace.spacesEtaleSite (reduction X) ⥤ EtaleOver X) :=
  NatIso.ofComponents (fun V ↦ ofAffineEtaleIsoOfSpacesEtale V) sorry

/-- The unit comparison of the affine étale identification, as a morphism of
functors of points. -/
def affineEtaleUnitHom (U : AffineEtaleOver X) :
    U.obj.left ⟶ (ofAffineEtale.obj (toAffineEtale.obj U)).obj.left :=
  unitHom (affineEtaleOverForget.obj U) ≫
    extensionAlongMap (toSpacesIsoToAffine U).hom

/-- `affineEtaleUnitHom U` is `unitHom` of the forgotten object, transported
along `toSpacesIsoToAffine`. -/
theorem affineEtaleUnitHom_def (U : AffineEtaleOver X) :
    affineEtaleUnitHom U =
      unitHom (affineEtaleOverForget.obj U) ≫
        extensionAlongMap (toSpacesIsoToAffine U).hom :=
  rfl

/-- The inverse unit comparison of the affine étale identification, as a
morphism of functors of points. -/
def affineEtaleUnitInv (U : AffineEtaleOver X) :
    (ofAffineEtale.obj (toAffineEtale.obj U)).obj.left ⟶ U.obj.left :=
  extensionAlongMap (toSpacesIsoToAffine U).inv ≫
    unitInv (affineEtaleOverForget.obj U)

/-- The unit isomorphism of the affine étale identification, at an object `U`. -/
def affineEtaleUnitIsoApp (U : AffineEtaleOver X) :
    U ≅ ofAffineEtale.obj (toAffineEtale.obj U) where
  hom := ⟨MorphismProperty.Over.homMk (affineEtaleUnitHom U) sorry trivial⟩
  inv := ⟨MorphismProperty.Over.homMk (affineEtaleUnitInv U) sorry trivial⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The unit isomorphism of the affine étale identification. -/
def affineEtaleUnitIso :
    𝟭 (AffineEtaleOver X) ≅ toAffineEtale ⋙ ofAffineEtale :=
  NatIso.ofComponents (fun U ↦ affineEtaleUnitIsoApp U) sorry

/-- The counit comparison on underlying schemes, as a morphism
`fibreAffineScheme (U_{V,ψ}) ⟶ V`. -/
def affineEtaleCounitSchemeHom
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    fibreAffineScheme (ofAffineEtale.obj V) ⟶ V.obj.left :=
  CategoryTheory.Yoneda.fullyFaithful.preimage
    ((fibreToReductionAlong (ofAffineEtale.obj V)).hom ≫
      counitHom (affineSpacesInclusion.obj V) :
      yoneda.obj (fibreAffineScheme (ofAffineEtale.obj V)) ⟶
        yoneda.obj V.obj.left)

/-- The inverse counit comparison on underlying schemes. -/
def affineEtaleCounitSchemeInv
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    V.obj.left ⟶ fibreAffineScheme (ofAffineEtale.obj V) :=
  CategoryTheory.Yoneda.fullyFaithful.preimage
    (counitInv (affineSpacesInclusion.obj V) ≫
      (fibreToReductionAlong (ofAffineEtale.obj V)).inv :
      yoneda.obj V.obj.left ⟶
        yoneda.obj (fibreAffineScheme (ofAffineEtale.obj V)))

/-- The counit isomorphism on underlying affine schemes
`U_{V,ψ} ×_X X_red ≅ V`. -/
def affineEtaleCounitSchemeIso
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    fibreAffineScheme (ofAffineEtale.obj V) ≅ V.obj.left where
  hom := affineEtaleCounitSchemeHom V
  inv := affineEtaleCounitSchemeInv V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `affineEtaleCounitSchemeIso V` is
`affineEtaleCounitSchemeHom V`. -/
@[simp]
theorem affineEtaleCounitSchemeIso_hom
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    (affineEtaleCounitSchemeIso V).hom = affineEtaleCounitSchemeHom V :=
  rfl

/-- The counit comparison lies over `X_red`. -/
theorem affineEtaleCounitIsoApp_w
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    AlgebraicSpace.ofOverMap (affineEtaleCounitSchemeIso V).hom ≫ V.obj.hom =
      fibreAffineSchemeHom (ofAffineEtale.obj V) :=
  sorry

/-- The inverse counit comparison lies over `X_red`. -/
theorem affineEtaleCounitIsoApp_inv_w
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    AlgebraicSpace.ofOverMap (affineEtaleCounitSchemeIso V).inv ≫
        fibreAffineSchemeHom (ofAffineEtale.obj V) =
      V.obj.hom :=
  sorry

/-- The counit isomorphism of the affine étale identification, at an object
`V`. -/
def affineEtaleCounitIsoApp
    (V : AlgebraicSpace.affineEtaleSite (reduction X)) :
    toAffineEtale.obj (ofAffineEtale.obj V) ≅ V where
  hom :=
    homMk
      (MorphismProperty.CostructuredArrow.homMk
        (affineEtaleCounitSchemeIso V).hom trivial (affineEtaleCounitIsoApp_w V))
  inv :=
    homMk
      (MorphismProperty.CostructuredArrow.homMk
        (affineEtaleCounitSchemeIso V).inv trivial
        (affineEtaleCounitIsoApp_inv_w V))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The counit isomorphism of the affine étale identification. -/
def affineEtaleCounitIso :
    ofAffineEtale ⋙ toAffineEtale ≅
      𝟭 (AlgebraicSpace.affineEtaleSite (reduction X)) :=
  NatIso.ofComponents (fun V ↦ affineEtaleCounitIsoApp V) sorry

/-- A morphism of affine formal algebraic spaces that is representable by
algebraic spaces and étale is representable by schemes. -/
theorem yoneda_relativelyRepresentable_of_affineEtale
    (hX :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X)
    {U : (Over S)ᵒᵖ ⥤ Type u} (φ : U ⟶ X) [Etale φ]
    (hU :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D U) :
    yoneda.relativelyRepresentable φ :=
  sorry

/-- Fibre products of an affine étale morphism of affine formal algebraic spaces
against affine schemes are affine. -/
theorem isAffine_pullback_of_affineEtale
    (hX :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X)
    {U : (Over S)ᵒᵖ ⥤ Type u} (φ : U ⟶ X) [Etale φ]
    (hU :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D U)
    {T : Over S} [IsAffine T.left] (ξ : yoneda.obj T ⟶ X)
    [hφ : (pullback ξ φ).IsRepresentable] :
    IsAffine (pullback ξ φ).reprX.left :=
  sorry

/-- Source-semantic companion of Lemma 87.19.7 in the functor-of-points layer:
an étale morphism of affine formal algebraic spaces is representable by schemes
and affine on affine-scheme pullbacks. -/
theorem affineEtale_representable_affine_spec
    (hX :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X)
    {U : (Over S)ᵒᵖ ⥤ Type u} (φ : U ⟶ X) [Etale φ]
    (hU :
      ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D U) :
    yoneda.relativelyRepresentable φ ∧
      ∀ {T : Over S} [IsAffine T.left] (ξ : yoneda.obj T ⟶ X)
        [hφ : (pullback ξ φ).IsRepresentable],
        IsAffine (pullback ξ φ).reprX.left :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
