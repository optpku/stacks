/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap59.Definition_59_33_2_EtaleLocalRing
public import stacks_project.Chap66.Definition_66_22_2_Point
public import stacks_project.Chap66.Definition_66_29_1_RingedSite

/-!
# Étale local rings of algebraic spaces

The étale local ring of an algebraic space at a geometric point is the stalk of the
structure sheaf on the small étale site at the associated site point.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The étale local ring of an algebraic space at a geometric point is the stalk of the
structure sheaf on the small étale site at that geometric point. The geometric point lies
over `xbar.image ∈ |X|`. -/
noncomputable abbrev etaleLocalRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) : Type u :=
  ((GeometricPoint.toSmallEtalePoint xbar).presheafFiber :
      ((smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
    (structureSheaf X).obj

/-- The étale local ring is definitionally the fiber of the small-étale structure sheaf. -/
theorem etaleLocalRing_def {S : Scheme.{u}} (X : AlgebraicSpace S) (xbar : GeometricPoint X) :
    etaleLocalRing X xbar =
      ((GeometricPoint.toSmallEtalePoint xbar).presheafFiber :
          ((smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
        (structureSheaf X).obj :=
  sorry

/-- The étale-site stalk is commutative, using the underlying ring operations of the
`RingCat` fiber. -/
instance etaleLocalRing.instCommRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) : CommRing (etaleLocalRing X xbar) :=
  { (inferInstance : Ring (etaleLocalRing X xbar)) with
    mul_comm := sorry }

/-- Recover the morphism in `Over S` underlying a morphism of represented algebraic spaces. -/
def toOverHom {S : Scheme.{u}} {U V : Over S} (φ : ofOver U ⟶ ofOver V) : U ⟶ V :=
  Yoneda.fullyFaithful.preimage (φ : yoneda.obj U ⟶ yoneda.obj V)

/-- `toOverHom` inverts `ofOverMap`. -/
theorem toOverHom_ofOverMap {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) :
    toOverHom (ofOverMap f) = f :=
  sorry

/-- The underlying scheme morphism of `toOverHom φ` is étale when `φ` is étale. -/
theorem etale_toOverHom_left {S : Scheme.{u}} {U : Over S}
    (V : smallEtaleSite (ofOver U)) :
    AlgebraicGeometry.Etale (toOverHom V.hom).left :=
  sorry

/-- Realize an object of the small étale site of `ofOver U` as an object of `U.left.Etale`. -/
def toSchemeEtale {S : Scheme.{u}} {U : Over S} (V : smallEtaleSite (ofOver U)) :
    U.left.Etale :=
  MorphismProperty.Over.mk ⊤ (toOverHom V.hom).left (etale_toOverHom_left V)

/-- The structure morphism of `toSchemeEtale V` is the underlying scheme map of `V.hom`. -/
theorem toSchemeEtale_hom {S : Scheme.{u}} {U : Over S} (V : smallEtaleSite (ofOver U)) :
    (toSchemeEtale V).hom = (toOverHom V.hom).left :=
  sorry

/-- Identity comparison of the underlying scheme of `V` with its scheme-étale realization. -/
def toSchemeEtale_schemeHom {S : Scheme.{u}} {U : Over S} (V : smallEtaleSite (ofOver U)) :
    (Scheme.smallEtaleToScheme U.left).obj (toSchemeEtale V) ⟶
      (smallEtaleToScheme (ofOver U)).obj V :=
  (𝟙 V.left.left :
    (Scheme.smallEtaleToScheme U.left).obj (toSchemeEtale V) ⟶
      (smallEtaleToScheme (ofOver U)).obj V)

/-- `toSchemeEtale_schemeHom` is the identity of the underlying scheme of `V`. -/
theorem toSchemeEtale_schemeHom_apply {S : Scheme.{u}} {U : Over S}
    (V : smallEtaleSite (ofOver U)) :
    toSchemeEtale_schemeHom V =
      (𝟙 V.left.left :
        (Scheme.smallEtaleToScheme U.left).obj (toSchemeEtale V) ⟶
          (smallEtaleToScheme (ofOver U)).obj V) :=
  sorry

/-- A lift of a geometric point through `V` determines a lift through `toSchemeEtale V`. -/
def toSchemeFiber {S : Scheme.{u}} {U : Over S} {p : GeometricPoint (ofOver U)}
    {V : smallEtaleSite (ofOver U)} (l : GeometricPoint.OverLift p V) :
    (@Scheme.pointSmallEtale U.left p.toScheme.K inferInstance
      (@IsSepClosed.of_isAlgClosed p.toScheme.K inferInstance
        p.toScheme.isAlgClosed) p.toScheme.hom).fiber.obj (toSchemeEtale V) :=
  Over.homMk (l.hom.left : (Over.mk p.toScheme.hom).left ⟶ (toSchemeEtale V).left) sorry

/-- The underlying scheme morphism of `toSchemeFiber l` is the underlying morphism of `l`. -/
theorem toSchemeFiber_left {S : Scheme.{u}} {U : Over S} {p : GeometricPoint (ofOver U)}
    {V : smallEtaleSite (ofOver U)} (l : GeometricPoint.OverLift p V) :
    (toSchemeFiber l).left = l.hom.left :=
  sorry

/-- `ofOverMap` of an étale morphism of schemes over `S` is étale as a morphism of algebraic
spaces. -/
theorem etale_ofSchemeEtale {S : Scheme.{u}} {U : Over S} (W : U.left.Etale) :
    Etale (ofOverMap (Over.homMk W.hom rfl : Over.mk (W.hom ≫ U.hom) ⟶ U)) :=
  sorry

/-- Realize an object of `U.left.Etale` as an object of the small étale site of `ofOver U`. -/
def ofSchemeEtale {S : Scheme.{u}} {U : Over S} (W : U.left.Etale) :
    smallEtaleSite (ofOver U) :=
  MorphismProperty.CostructuredArrow.mk ⊤
    (ofOverMap (Over.homMk W.hom rfl : Over.mk (W.hom ≫ U.hom) ⟶ U))
    (etale_ofSchemeEtale W)

/-- The structure morphism of `ofSchemeEtale W` is `ofOverMap` of the over-morphism of `W`. -/
theorem ofSchemeEtale_hom {S : Scheme.{u}} {U : Over S} (W : U.left.Etale) :
    (ofSchemeEtale W).hom =
      ofOverMap (Over.homMk W.hom rfl : Over.mk (W.hom ≫ U.hom) ⟶ U) :=
  sorry

/-- Identity comparison of the underlying scheme of `W` with its algebraic-space realization. -/
def ofSchemeEtale_schemeHom {S : Scheme.{u}} {U : Over S} (W : U.left.Etale) :
    (smallEtaleToScheme (ofOver U)).obj (ofSchemeEtale W) ⟶
      (Scheme.smallEtaleToScheme U.left).obj W :=
  (𝟙 W.left :
    (smallEtaleToScheme (ofOver U)).obj (ofSchemeEtale W) ⟶
      (Scheme.smallEtaleToScheme U.left).obj W)

/-- `ofSchemeEtale_schemeHom` is the identity of the underlying scheme of `W`. -/
theorem ofSchemeEtale_schemeHom_apply {S : Scheme.{u}} {U : Over S} (W : U.left.Etale) :
    ofSchemeEtale_schemeHom W =
      (𝟙 W.left :
        (smallEtaleToScheme (ofOver U)).obj (ofSchemeEtale W) ⟶
          (Scheme.smallEtaleToScheme U.left).obj W) :=
  sorry

/-- A scheme-étale lift of `p.toScheme` determines a lift through `ofSchemeEtale W`. -/
def ofSchemeFiber {S : Scheme.{u}} {U : Over S} {p : GeometricPoint (ofOver U)}
    {W : U.left.Etale}
    (t : (@Scheme.pointSmallEtale U.left p.toScheme.K inferInstance
      (@IsSepClosed.of_isAlgClosed p.toScheme.K inferInstance
        p.toScheme.isAlgClosed) p.toScheme.hom).fiber.obj W) :
    GeometricPoint.OverLift p (ofSchemeEtale W) :=
  GeometricPoint.OverLift.of
    (Over.homMk (t.left : (Over.mk p.structureHom).left ⟶ (ofSchemeEtale W).left.left) sorry)
    sorry

/-- The underlying scheme morphism of `ofSchemeFiber t` is the underlying morphism of `t`. -/
theorem ofSchemeFiber_hom_left {S : Scheme.{u}} {U : Over S} {p : GeometricPoint (ofOver U)}
    {W : U.left.Etale}
    (t : (@Scheme.pointSmallEtale U.left p.toScheme.K inferInstance
      (@IsSepClosed.of_isAlgClosed p.toScheme.K inferInstance
        p.toScheme.isAlgClosed) p.toScheme.hom).fiber.obj W) :
    (ofSchemeFiber t).hom.left = t.left :=
  sorry

/-- Canonical `RingCat` comparison from the algebraic-space étale stalk to the scheme étale
stalk of a represented algebraic space. -/
def etaleLocalRing_ofOver_hom {S : Scheme.{u}} {U : Over S} (p : GeometricPoint (ofOver U)) :
    ((GeometricPoint.toSmallEtalePoint p).presheafFiber :
        ((smallEtaleSite (ofOver U))ᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
      (structureSheaf (ofOver U)).obj ⟶
      ((@Scheme.pointSmallEtale U.left p.toScheme.K inferInstance
          (@IsSepClosed.of_isAlgClosed p.toScheme.K inferInstance
            p.toScheme.isAlgClosed) p.toScheme.hom).presheafFiber :
          (U.left.Etaleᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
        (Scheme.Etale.Small.structureSheaf U.left).obj :=
  (GeometricPoint.toSmallEtalePoint p).presheafFiberDesc
    (fun V l ↦
      (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map (toSchemeEtale_schemeHom V).op ≫
        (@Scheme.pointSmallEtale U.left p.toScheme.K inferInstance
          (@IsSepClosed.of_isAlgClosed p.toScheme.K inferInstance
            p.toScheme.isAlgClosed) p.toScheme.hom).toPresheafFiber (toSchemeEtale V)
          (toSchemeFiber l) (Scheme.Etale.Small.structureSheaf U.left).obj)
    sorry

/-- Canonical `RingCat` comparison from the scheme étale stalk of `U.left` to the
algebraic-space étale stalk of `ofOver U`. -/
def etaleLocalRing_ofOver_inv {S : Scheme.{u}} {U : Over S} (p : GeometricPoint (ofOver U)) :
    ((@Scheme.pointSmallEtale U.left p.toScheme.K inferInstance
        (@IsSepClosed.of_isAlgClosed p.toScheme.K inferInstance
          p.toScheme.isAlgClosed) p.toScheme.hom).presheafFiber :
        (U.left.Etaleᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
      (Scheme.Etale.Small.structureSheaf U.left).obj ⟶
      ((GeometricPoint.toSmallEtalePoint p).presheafFiber :
          ((smallEtaleSite (ofOver U))ᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u}).obj
        (structureSheaf (ofOver U)).obj :=
  (@Scheme.pointSmallEtale U.left p.toScheme.K inferInstance
    (@IsSepClosed.of_isAlgClosed p.toScheme.K inferInstance
      p.toScheme.isAlgClosed) p.toScheme.hom).presheafFiberDesc
    (fun W t ↦
      (Scheme.Γ ⋙ forget₂ CommRingCat RingCat).map (ofSchemeEtale_schemeHom W).op ≫
        (GeometricPoint.toSmallEtalePoint p).toPresheafFiber (ofSchemeEtale W)
          (ofSchemeFiber t) (structureSheaf (ofOver U)).obj)
    sorry

/-- The two `RingCat` comparisons of étale stalks are inverse. -/
theorem etaleLocalRing_ofOver_hom_comp {S : Scheme.{u}} {U : Over S}
    (p : GeometricPoint (ofOver U)) :
    etaleLocalRing_ofOver_hom p ≫ etaleLocalRing_ofOver_inv p = 𝟙 _ :=
  sorry

/-- The reverse `RingCat` comparison is a left inverse of `etaleLocalRing_ofOver_hom`. -/
theorem etaleLocalRing_ofOver_inv_comp {S : Scheme.{u}} {U : Over S}
    (p : GeometricPoint (ofOver U)) :
    etaleLocalRing_ofOver_inv p ≫ etaleLocalRing_ofOver_hom p = 𝟙 _ :=
  sorry

/-- The étale local ring of an algebraic space represented by a scheme `U` over `S`
identifies with the étale local ring of `U.left` at the corresponding geometric point. -/
noncomputable def etaleLocalRing_ofOver {S : Scheme.{u}} {U : Over S}
    (p : GeometricPoint (ofOver U)) :
    etaleLocalRing (ofOver U) p ≃+* Scheme.etaleLocalRing U.left p.toScheme :=
  RingEquiv.ofRingHom (RingCat.Hom.hom (etaleLocalRing_ofOver_hom p))
    (RingCat.Hom.hom (etaleLocalRing_ofOver_inv p)) sorry sorry

/-- The forward map of `etaleLocalRing_ofOver` is the `RingCat` comparison of étale stalks. -/
theorem etaleLocalRing_ofOver_apply {S : Scheme.{u}} {U : Over S}
    (p : GeometricPoint (ofOver U)) (x : etaleLocalRing (ofOver U) p) :
    etaleLocalRing_ofOver p x = RingCat.Hom.hom (etaleLocalRing_ofOver_hom p) x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
