/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Algebra.Field.Equiv
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Residue fields of points of scheme pullbacks

This leaf owns the residue-field comparison maps attached to the prime of a
tensor product of residue fields which represents a point of a scheme fibre
product.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Pullback

variable {X Y S : Scheme.{u}}
variable {f : X ⟶ S} {g : Y ⟶ S}

namespace SpecOfPoint

/-- The prime associated to a point of a scheme pullback is the image of the closed point of
its residue field under the canonical tensor-product map. -/
@[stacks 01JT, simp]
theorem eq_map_closedPoint (z : (pullback f g : Scheme)) :
    SpecOfPoint z =
      Spec.map (ofPointTensor z)
        (closedPoint ((pullback f g : Scheme).residueField z)) := sorry

/-- The canonical morphism from the residue field of `SpecOfPoint z` to the residue field of
the corresponding point `z` of the scheme pullback. -/
@[stacks 01JT]
noncomputable def residueFieldMap
    (z : (pullback f g : Scheme)) :
    CommRingCat.of (SpecOfPoint z).asIdeal.ResidueField ⟶
      (pullback f g : Scheme).residueField z :=
  CommRingCat.ofHom <|
    ((Ideal.algEquivResidueFieldOfField
        (⊥ : Ideal ((pullback f g : Scheme).residueField z))).symm.toRingHom).comp
      (Ideal.ResidueField.map (SpecOfPoint z).asIdeal
        (⊥ : Ideal ((pullback f g : Scheme).residueField z))
        (ofPointTensor z).hom rfl)

/-- The pullback-point residue-field comparison factors the tensor-product map through the
residue field of its associated prime. -/
@[reassoc, stacks 01JT "pullback-point residue-field factorization"]
theorem algebraMap_residueFieldMap
    (z : (pullback f g : Scheme)) :
    CommRingCat.ofHom
          (algebraMap (Triplet.ofPoint z).tensor
            (SpecOfPoint z).asIdeal.ResidueField) ≫
        residueFieldMap z =
      ofPointTensor z := sorry

/-- The residue-field comparison attached to a point of a scheme pullback is an isomorphism of
commutative rings. -/
@[stacks 01JT]
theorem residueFieldMap_isIso
    (z : (pullback f g : Scheme)) :
    IsIso (residueFieldMap z) := sorry

/-- The underlying ring homomorphism of the pullback residue-field
comparison is bijective. -/
@[stacks 01JT]
theorem residueFieldMap_bijective
    (z : (pullback f g : Scheme)) :
    Function.Bijective (residueFieldMap z).hom := sorry

/-- The `Spec` map of `residueFieldMap z` is compatible with the canonical maps from the
residue-field spectrum of `SpecOfPoint z` to the tensor-product spectrum. -/
@[stacks 01JT]
theorem residueFieldMap_spec
    (z : (pullback f g : Scheme)) :
    CommSq
      (Spec.map (residueFieldMap z))
      (Spec.map (ofPointTensor z))
      (Spec.map (Scheme.Spec.residueFieldIso (Triplet.ofPoint z).tensor (SpecOfPoint z)).hom ≫
        (Spec (Triplet.ofPoint z).tensor).fromSpecResidueField (SpecOfPoint z))
      (𝟙 _) := sorry

end SpecOfPoint

/-- The residue fields at two points over the same base point are canonically equivalent once
the two residue-field maps from the base are specified to be bijective. -/
noncomputable def residueFieldEquivOfBaseMapBijective
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) (hxy : f x = g y)
    (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    X.residueField x ≃+* Y.residueField y :=
  let ex : S.residueField (f x) ≃+* X.residueField x :=
    RingEquiv.ofBijective (f.residueFieldMap x).hom hx
  let es : S.residueField (f x) ≃+* S.residueField (g y) :=
    (S.residueFieldCongr hxy).commRingCatIsoToRingEquiv
  let ey : S.residueField (g y) ≃+* Y.residueField y :=
    RingEquiv.ofBijective (g.residueFieldMap y).hom hy
  ex.symm.trans (es.trans ey)

/-- Evaluation of the tensor product of the two point residue fields in the first residue
field, using the specified identifications with the base residue field. -/
noncomputable def pointTensorEvaluation
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) (hxy : f x = g y)
    (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    (Triplet.mk' x y hxy).tensor ⟶ X.residueField x :=
  pushout.desc (𝟙 _)
    (CommRingCat.ofHom
      (residueFieldEquivOfBaseMapBijective f g x y hxy hx hy).symm.toRingHom)
    (by
      let ex : S.residueField (f x) ≃+* X.residueField x :=
        RingEquiv.ofBijective (f.residueFieldMap x).hom hx
      let es : S.residueField (f x) ≃+* S.residueField (g y) :=
        (S.residueFieldCongr hxy).commRingCatIsoToRingEquiv
      let ey : S.residueField (g y) ≃+* Y.residueField y :=
        RingEquiv.ofBijective (g.residueFieldMap y).hom hy
      ext a
      change ex (es.symm a) = (ex.symm.trans (es.trans ey)).symm (ey a)
      simp)

/-- The kernel of tensor evaluation at two residue-field-identical points is prime. -/
theorem pointTensorEvaluation_ker_isPrime
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) (hxy : f x = g y)
    (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    (RingHom.ker (pointTensorEvaluation f g x y hxy hx hy).hom).IsPrime := sorry

/-- The point of a scheme pullback selected by evaluation of the tensor product of residue
fields at two points whose residue fields agree with that of their common image. -/
noncomputable def pointOfBaseResidueFieldMapBijective
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) (hxy : f x = g y)
    (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    (pullback f g : Scheme) :=
  carrierEquiv.symm
    ⟨Triplet.mk' x y hxy,
      ⟨RingHom.ker (pointTensorEvaluation f g x y hxy hx hy).hom,
        pointTensorEvaluation_ker_isPrime f g x y hxy hx hy⟩⟩

/-- The first projection of the evaluation-selected pullback point is the first given point. -/
theorem pointOfBaseResidueFieldMapBijective_fst
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) (hxy : f x = g y)
    (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    pullback.fst f g (pointOfBaseResidueFieldMapBijective f g x y hxy hx hy) = x := sorry

/-- The second projection of the evaluation-selected pullback point is the second given point. -/
theorem pointOfBaseResidueFieldMapBijective_snd
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) (hxy : f x = g y)
    (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    pullback.snd f g (pointOfBaseResidueFieldMapBijective f g x y hxy hx hy) = y := sorry

/-- The first projection from a pullback induces a bijection on residue fields at any point
whose two coordinates have residue fields equal to that of their common image. -/
theorem fst_residueFieldMap_bijective_of_base
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom)
    (xy : (pullback f g : Scheme)) (hfstxy : pullback.fst f g xy = x)
    (hsndxy : pullback.snd f g xy = y) :
    Function.Bijective ((pullback.fst f g).residueFieldMap xy).hom := sorry

/-- The second projection from a pullback induces a bijection on residue fields at any point
whose two coordinates have residue fields equal to that of their common image. -/
theorem snd_residueFieldMap_bijective_of_base
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom)
    (xy : (pullback f g : Scheme)) (hfstxy : pullback.fst f g xy = x)
    (hsndxy : pullback.snd f g xy = y) :
    Function.Bijective ((pullback.snd f g).residueFieldMap xy).hom := sorry

/-- Compatible points have a unique lift to a scheme pullback when the residue-field map
at the point on the right is an isomorphism. -/
theorem existsUnique_point_of_rightResidueFieldIso
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) (hxy : f x = g y)
    [IsIso (g.residueFieldMap y)] :
    ∃! p : (pullback f g : Scheme),
      pullback.fst f g p = x ∧ pullback.snd f g p = y := sorry

/-- The first projection from a pullback induces a bijection on residue fields when the
residue-field map at the point on the right is an isomorphism. -/
theorem fst_residueFieldMap_bijective_of_rightResidueFieldIso
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (xy : (pullback f g : Scheme)) (hfstxy : pullback.fst f g xy = x)
    (hsndxy : pullback.snd f g xy = y) [IsIso (g.residueFieldMap y)] :
    Function.Bijective ((pullback.fst f g).residueFieldMap xy).hom := sorry

/-- The first projection induces the canonical map from the residue field of the first point to
the residue field of the evaluation-selected pullback point. -/
noncomputable def pointFstResidueFieldMap
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y) (hxy : f x = g y)
    (hx : Function.Bijective (f.residueFieldMap x).hom)
    (hy : Function.Bijective (g.residueFieldMap y).hom) :
    X.residueField x ⟶
      (pullback f g : Scheme).residueField
        (pointOfBaseResidueFieldMapBijective f g x y hxy hx hy) :=
  let xy := pointOfBaseResidueFieldMapBijective f g x y hxy hx hy
  let hfstxy := pointOfBaseResidueFieldMapBijective_fst f g x y hxy hx hy
  (X.residueFieldCongr hfstxy).inv ≫ (pullback.fst f g).residueFieldMap xy

end AlgebraicGeometry.Scheme.Pullback
