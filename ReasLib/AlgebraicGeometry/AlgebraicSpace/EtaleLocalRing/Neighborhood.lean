module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalRing
public import ReasLib.CategoryTheory.Limits.Over.Products
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Yoneda

/-!
# Comparison of étale local rings along a scheme étale neighbourhood

An étale neighbourhood `(U, ubar)` of a geometric point `xbar` of an algebraic space `X`, with
`U` a scheme, identifies the étale-site stalk `𝒪_{X, xbar}` with the scheme étale-site stalk
`𝒪_{U, ubar}`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open Functor.relativelyRepresentable

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace GeometricPoint.SmallEtaleNeighborhood

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {xbar : GeometricPoint X}

/-- The underlying scheme of an étale neighbourhood in the small étale site. -/
abbrev scheme (N : SmallEtaleNeighborhood xbar) : Scheme.{u} :=
  N.toSite.left.left

/-- The underlying scheme of an étale neighbourhood is the domain of its structure morphism
over `S`. -/
theorem scheme_def (N : SmallEtaleNeighborhood xbar) :
    N.scheme = N.toSite.left.left :=
  rfl

/-- The geometric point of the neighbourhood scheme induced by the chosen lift of `xbar`. -/
def schemeGeometricPoint (N : SmallEtaleNeighborhood xbar) :
    Scheme.GeometricPoint N.scheme where
  toFieldValuedPoint := Scheme.FieldValuedPoint.of xbar.K N.overHom.left
  isAlgClosed := xbar.isAlgClosed

/-- The scheme morphism of `schemeGeometricPoint N` is the underlying morphism of the chosen
lift. -/
theorem schemeGeometricPoint_hom (N : SmallEtaleNeighborhood xbar) :
    (schemeGeometricPoint N).hom = N.overHom.left :=
  rfl

/-- The center of the neighbourhood geometric point, as a point of the neighbourhood scheme. -/
abbrev center (N : SmallEtaleNeighborhood xbar) : N.scheme :=
  (schemeGeometricPoint N).image

/-- The center of an étale neighbourhood is the image of its scheme geometric point. -/
theorem center_eq_image (N : SmallEtaleNeighborhood xbar) :
    N.center = (schemeGeometricPoint N).image :=
  rfl

/-- Realize a scheme étale over the neighbourhood scheme as an object of the small étale site
of `X`. -/
def ofSchemeEtale (N : SmallEtaleNeighborhood xbar) (W : N.scheme.Etale) :
    smallEtaleSite X :=
  smallEtaleSite.mk
    (ofOverMap (Over.homMk W.hom rfl :
      Over.mk (W.hom ≫ N.toSite.left.hom) ⟶ N.toSite.left) ≫ N.toSite.hom)
    (by sorry)

/-- The structural arrow of a postcomposed scheme-étale object is the composite of its
scheme arrow with the neighbourhood structure morphism. -/
theorem ofSchemeEtale_eq (N : SmallEtaleNeighborhood xbar) (W : N.scheme.Etale) :
    (ofSchemeEtale N W).hom =
      ofOverMap (Over.homMk W.hom rfl :
        Over.mk (W.hom ≫ N.toSite.left.hom) ⟶ N.toSite.left) ≫ N.toSite.hom :=
  rfl

/-- Identity comparison of the underlying scheme of `W` with its realization in the small étale
site of `X`. -/
def ofSchemeEtale_schemeHom (N : SmallEtaleNeighborhood xbar) (W : N.scheme.Etale) :
    (smallEtaleToScheme X).obj (ofSchemeEtale N W) ⟶
      (Scheme.smallEtaleToScheme N.scheme).obj W :=
  (𝟙 W.left :
    (smallEtaleToScheme X).obj (ofSchemeEtale N W) ⟶
      (Scheme.smallEtaleToScheme N.scheme).obj W)

/-- `ofSchemeEtale_schemeHom` is the identity of the underlying scheme of `W`. -/
theorem ofSchemeEtale_schemeHom_apply (N : SmallEtaleNeighborhood xbar) (W : N.scheme.Etale) :
    ofSchemeEtale_schemeHom N W =
      (𝟙 W.left :
        (smallEtaleToScheme X).obj (ofSchemeEtale N W) ⟶
          (Scheme.smallEtaleToScheme N.scheme).obj W) :=
  rfl

/-- A scheme-étale lift of `schemeGeometricPoint N` determines a lift of `xbar` through
`ofSchemeEtale N W`. -/
def ofSchemeFiber (N : SmallEtaleNeighborhood xbar) {W : N.scheme.Etale}
    (t : (@Scheme.pointSmallEtale N.scheme (schemeGeometricPoint N).K inferInstance
      (@IsSepClosed.of_isAlgClosed (schemeGeometricPoint N).K inferInstance
        (schemeGeometricPoint N).isAlgClosed) (schemeGeometricPoint N).hom).fiber.obj W) :
    OverLift xbar (ofSchemeEtale N W) :=
  let compatibility :
      (t.left ≫ (W.hom ≫ N.toSite.left.hom) = xbar.structureHom) ∧
      (∀ h : t.left ≫ (W.hom ≫ N.toSite.left.hom) = xbar.structureHom,
        ofOverMap (Over.homMk t.left h :
          Over.mk xbar.structureHom ⟶ (ofSchemeEtale N W).left) ≫
            (ofSchemeEtale N W).hom = xbar.hom) := by
    sorry
  OverLift.of (Over.homMk t.left compatibility.1) (compatibility.2 compatibility.1)

/-- The underlying scheme morphism of `ofSchemeFiber N t` is the underlying morphism of `t`. -/
theorem ofSchemeFiber_hom_left (N : SmallEtaleNeighborhood xbar) {W : N.scheme.Etale}
    (t : (@Scheme.pointSmallEtale N.scheme (schemeGeometricPoint N).K inferInstance
      (@IsSepClosed.of_isAlgClosed (schemeGeometricPoint N).K inferInstance
        (schemeGeometricPoint N).isAlgClosed) (schemeGeometricPoint N).hom).fiber.obj W) :
    (ofSchemeFiber N t).hom.left = t.left :=
  rfl

/-- Realize an object of the small étale site of `X` as a scheme étale over the neighbourhood
scheme, by base change along the neighbourhood structure morphism. -/
def toSchemeEtale (N : SmallEtaleNeighborhood xbar) (V : smallEtaleSite X) :
    N.scheme.Etale :=
  MorphismProperty.Over.mk ⊤
    (Yoneda.fullyFaithful.preimage
      ((of_diag X.representableDiagonal N.toSite.hom).fst V.hom)).left
    (by sorry)

/-- The scheme arrow of the base-changed étale object is the Yoneda preimage of the first
represented pullback projection. -/
theorem toSchemeEtale_eq (N : SmallEtaleNeighborhood xbar) (V : smallEtaleSite X) :
    (toSchemeEtale N V).hom =
      (Yoneda.fullyFaithful.preimage
        ((of_diag X.representableDiagonal N.toSite.hom).fst V.hom)).left :=
  rfl

/-- The underlying scheme morphism from the base-changed neighbourhood object to `V`. -/
def toSchemeEtale_schemeHom (N : SmallEtaleNeighborhood xbar) (V : smallEtaleSite X) :
    (Scheme.smallEtaleToScheme N.scheme).obj (toSchemeEtale N V) ⟶
      (smallEtaleToScheme X).obj V :=
  ((of_diag X.representableDiagonal N.toSite.hom).snd V.hom).left

/-- `toSchemeEtale_schemeHom` is the represented pullback projection to the underlying scheme
of `V`. -/
theorem toSchemeEtale_schemeHom_apply (N : SmallEtaleNeighborhood xbar) (V : smallEtaleSite X) :
    toSchemeEtale_schemeHom N V = ((of_diag X.representableDiagonal N.toSite.hom).snd V.hom).left :=
  rfl

/-- The represented pullback lift of `N.overHom` and a lift of `xbar` through `V`. -/
def toSchemeFiberLift (N : SmallEtaleNeighborhood xbar) {V : smallEtaleSite X}
    (l : OverLift xbar V) :
    Over.mk xbar.structureHom ⟶ (of_diag X.representableDiagonal N.toSite.hom).pullback V.hom :=
  (of_diag X.representableDiagonal N.toSite.hom).lift (yoneda.map N.overHom) l.hom sorry

/-- The represented pullback lift projects to the supplied lift `l.hom` of `xbar`. -/
theorem toSchemeFiberLift_snd (N : SmallEtaleNeighborhood xbar) {V : smallEtaleSite X}
    (l : OverLift xbar V) :
    toSchemeFiberLift N l ≫ (of_diag X.representableDiagonal N.toSite.hom).snd V.hom = l.hom :=
  sorry

/-- A lift of `xbar` through `V` determines a lift of `schemeGeometricPoint N` through the
base change of `V` to the neighbourhood scheme. -/
def toSchemeFiber (N : SmallEtaleNeighborhood xbar) {V : smallEtaleSite X}
    (l : OverLift xbar V) :
    (@Scheme.pointSmallEtale N.scheme (schemeGeometricPoint N).K inferInstance
      (@IsSepClosed.of_isAlgClosed (schemeGeometricPoint N).K inferInstance
        (schemeGeometricPoint N).isAlgClosed) (schemeGeometricPoint N).hom).fiber.obj
      (toSchemeEtale N V) :=
  Over.homMk (toSchemeFiberLift N l).left sorry

/-- The underlying scheme morphism of `toSchemeFiber N l` is the underlying morphism of
`toSchemeFiberLift N l`. -/
theorem toSchemeFiber_left (N : SmallEtaleNeighborhood xbar) {V : smallEtaleSite X}
    (l : OverLift xbar V) :
    (toSchemeFiber N l).left = (toSchemeFiberLift N l).left :=
  rfl

end GeometricPoint.SmallEtaleNeighborhood

open GeometricPoint GeometricPoint.SmallEtaleNeighborhood

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {xbar : GeometricPoint X}

/-- Canonical `RingCat` comparison from the algebraic-space étale stalk at `xbar` to the scheme
étale stalk of an étale neighbourhood. -/
def etaleLocalRing_etaleNeighborhood_hom (N : SmallEtaleNeighborhood xbar) :
    ((GeometricPoint.toSmallEtalePoint xbar).presheafFiber :
        ((smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
      (structureSheaf X).obj ⟶
      ((@Scheme.pointSmallEtale N.scheme (schemeGeometricPoint N).K inferInstance
          (@IsSepClosed.of_isAlgClosed (schemeGeometricPoint N).K inferInstance
            (schemeGeometricPoint N).isAlgClosed) (schemeGeometricPoint N).hom).presheafFiber :
          (N.scheme.Etaleᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
        (Scheme.Etale.Small.structureSheaf N.scheme).obj :=
  (GeometricPoint.toSmallEtalePoint xbar).presheafFiberDesc
    (fun V l ↦
      (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map
          (SmallEtaleNeighborhood.toSchemeEtale_schemeHom N V).op ≫
        (@Scheme.pointSmallEtale N.scheme (schemeGeometricPoint N).K inferInstance
          (@IsSepClosed.of_isAlgClosed (schemeGeometricPoint N).K inferInstance
            (schemeGeometricPoint N).isAlgClosed) (schemeGeometricPoint N).hom).toPresheafFiber
          (SmallEtaleNeighborhood.toSchemeEtale N V)
          (SmallEtaleNeighborhood.toSchemeFiber N l)
          (Scheme.Etale.Small.structureSheaf N.scheme).obj)
    sorry

/-- Canonical `RingCat` comparison from the scheme étale stalk of an étale neighbourhood to the
algebraic-space étale stalk at `xbar`. -/
def etaleLocalRing_etaleNeighborhood_inv (N : SmallEtaleNeighborhood xbar) :
    ((@Scheme.pointSmallEtale N.scheme (schemeGeometricPoint N).K inferInstance
        (@IsSepClosed.of_isAlgClosed (schemeGeometricPoint N).K inferInstance
          (schemeGeometricPoint N).isAlgClosed) (schemeGeometricPoint N).hom).presheafFiber :
        (N.scheme.Etaleᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
      (Scheme.Etale.Small.structureSheaf N.scheme).obj ⟶
      ((GeometricPoint.toSmallEtalePoint xbar).presheafFiber :
          ((smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
        (structureSheaf X).obj :=
  (@Scheme.pointSmallEtale N.scheme (schemeGeometricPoint N).K inferInstance
    (@IsSepClosed.of_isAlgClosed (schemeGeometricPoint N).K inferInstance
      (schemeGeometricPoint N).isAlgClosed) (schemeGeometricPoint N).hom).presheafFiberDesc
    (fun W t ↦
      (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map
          (SmallEtaleNeighborhood.ofSchemeEtale_schemeHom N W).op ≫
        (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber
          (SmallEtaleNeighborhood.ofSchemeEtale N W)
          (SmallEtaleNeighborhood.ofSchemeFiber N t) (structureSheaf X).obj)
    sorry

/-- The two `RingCat` comparisons of étale stalks along an étale neighbourhood are inverse. -/
theorem etaleLocalRing_etaleNeighborhood_hom_comp (N : SmallEtaleNeighborhood xbar) :
    etaleLocalRing_etaleNeighborhood_hom N ≫ etaleLocalRing_etaleNeighborhood_inv N = 𝟙 _ :=
  sorry

/-- The reverse `RingCat` comparison is a left inverse of `etaleLocalRing_etaleNeighborhood_hom`. -/
theorem etaleLocalRing_etaleNeighborhood_inv_comp (N : SmallEtaleNeighborhood xbar) :
    etaleLocalRing_etaleNeighborhood_inv N ≫ etaleLocalRing_etaleNeighborhood_hom N = 𝟙 _ :=
  sorry

/-- The étale local ring of an algebraic space at a geometric point identifies with the étale
local ring of a scheme étale neighbourhood at the induced geometric point. -/
def etaleLocalRing_etaleNeighborhood (N : SmallEtaleNeighborhood xbar) :
    etaleLocalRing X xbar ≃+* Scheme.etaleLocalRing N.scheme (schemeGeometricPoint N) :=
  RingEquiv.ofRingHom (RingCat.Hom.hom (etaleLocalRing_etaleNeighborhood_hom N))
    (RingCat.Hom.hom (etaleLocalRing_etaleNeighborhood_inv N))
    (congrArg RingCat.Hom.hom (etaleLocalRing_etaleNeighborhood_inv_comp N))
    (congrArg RingCat.Hom.hom (etaleLocalRing_etaleNeighborhood_hom_comp N))

/-- The forward map of `etaleLocalRing_etaleNeighborhood` is the `RingCat` comparison of étale
stalks. -/
theorem etaleLocalRing_etaleNeighborhood_apply (N : SmallEtaleNeighborhood xbar)
    (x : etaleLocalRing X xbar) :
    etaleLocalRing_etaleNeighborhood N x =
      RingCat.Hom.hom (etaleLocalRing_etaleNeighborhood_hom N) x :=
  rfl

/-- The reverse map of `etaleLocalRing_etaleNeighborhood` is the reverse `RingCat` comparison of
étale stalks. -/
theorem etaleLocalRing_etaleNeighborhood_symm_apply (N : SmallEtaleNeighborhood xbar)
    (x : Scheme.etaleLocalRing N.scheme (schemeGeometricPoint N)) :
    (etaleLocalRing_etaleNeighborhood N).symm x =
      RingCat.Hom.hom (etaleLocalRing_etaleNeighborhood_inv N) x :=
  rfl

namespace etaleLocalRing_etaleNeighborhood

/-- Canonical comparison from the Zariski local ring of the neighbourhood scheme at the center
to the étale local ring of `X` at `xbar`. -/
def fromZariskiStalk (N : SmallEtaleNeighborhood xbar) :
    N.scheme.presheaf.stalk N.center →+* etaleLocalRing X xbar :=
  (etaleLocalRing_etaleNeighborhood N).symm.toRingHom.comp
    (Scheme.etaleLocalRing.fromZariskiStalk N.scheme (schemeGeometricPoint N))

/-- `fromZariskiStalk` is the scheme-level Zariski-to-étale comparison followed by the reverse
neighbourhood identification. -/
theorem fromZariskiStalk_comp (N : SmallEtaleNeighborhood xbar) :
    fromZariskiStalk N =
      (etaleLocalRing_etaleNeighborhood N).symm.toRingHom.comp
        (Scheme.etaleLocalRing.fromZariskiStalk N.scheme (schemeGeometricPoint N)) :=
  rfl

end etaleLocalRing_etaleNeighborhood

end AlgebraicGeometry.AlgebraicSpace
