/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Gluing.Points
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.RingTheory.Pullback.Surjective

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteExtensionCurve

/-- The pullback situation presenting the coefficient ring of a finite extension curve. -/
def pullbackSituation (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    SurjectiveRingPullbackSituation k k' (Polynomial k') :=
  SurjectiveRingPullbackSituation.ofSurjective (algebraMap k k')
    (Polynomial.evalRingHom (0 : k')) (Polynomial.eval_surjective (0 : k'))

/-- The pullback situation uses the extension map and evaluation at zero. -/
theorem pullbackSituation_spec (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (pullbackSituation k k').toA = algebraMap k k' ∧
      (pullbackSituation k k').fromAprime = Polynomial.evalRingHom (0 : k') := sorry

/-- The polynomial subring whose constant coefficient lies in the ground-field image. -/
def coefficientSubring (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Subring (Polynomial k') :=
  Subring.comap (Polynomial.evalRingHom (0 : k')) (RingHom.range (algebraMap k k'))

/-- The canonical pullback ring `k ×_{k'} k'[x]` for the coefficient-ring construction. -/
abbrev coefficientRing (k k' : Type u) [Field k] [Field k'] [Algebra k k'] : Type u :=
  (pullbackSituation k k').Bprime

/-- The polynomial projection of a pullback element lies in the displayed coefficient subring. -/
theorem coefficientRing_snd_mem (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (z : coefficientRing k k') :
    (pullbackSituation k k').bprimeToAprime z ∈ coefficientSubring k k' := sorry

/-- The canonical map from the pullback to the displayed polynomial subring. -/
def coefficientRing_toSubring (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    coefficientRing k k' →+* coefficientSubring k k' :=
  ((pullbackSituation k k').bprimeToAprime).codRestrict
    (coefficientSubring k k') (coefficientRing_snd_mem k k')

/-- The polynomial-subring realization has the same elements as the pullback ring. -/
theorem coefficientRing_toSubring_bijective (k k' : Type u)
    [Field k] [Field k'] [Algebra k k'] :
    Function.Bijective (coefficientRing_toSubring k k') := sorry

/-- Evaluation at zero commutes with the coefficient extension on polynomials. -/
theorem coefficientPolynomialMap_comm (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)) ≫
        CommRingCat.ofHom (algebraMap k k') =
      CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k')) ≫
        CommRingCat.ofHom (Polynomial.evalRingHom (0 : k')) := sorry

/-- The polynomial map induced by the two legs of the coefficient-ring pullback. -/
def coefficientPolynomialMap (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Polynomial k →+* coefficientRing k k' :=
  (pullback.lift
    (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))
    (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k')))
    (coefficientPolynomialMap_comm k k')).hom

/-- The ground-field map into the coefficient pullback, used for its affine chart. -/
def coefficientBaseMap (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    k →+* coefficientRing k k' :=
  (coefficientPolynomialMap k k').comp (Polynomial.C : k →+* Polynomial k)

/-- Membership in `coefficientSubring` means that evaluation at zero comes from `k`. -/
theorem coefficientSubring_mem_iff (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (f : Polynomial k') :
    f ∈ coefficientSubring k k' ↔ Polynomial.eval 0 f ∈ RingHom.range (algebraMap k k') := sorry

/-- The distinguished polynomial coordinate `x` in the pullback coefficient ring. -/
def x (k k' : Type u) [Field k] [Field k'] [Algebra k k'] : coefficientRing k k' :=
  coefficientPolynomialMap k k' Polynomial.X

/-- The polynomial coordinate `y` on the second affine chart. -/
def y (k' : Type u) [Field k'] : Polynomial k' := Polynomial.X

/-- The distinguished ideal, given by the kernel of the projection to `k`. -/
def distinguishedIdeal (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Ideal (coefficientRing k k') :=
  RingHom.ker (pullbackSituation k k').bprimeToB

/-- The projections of `x` have ground-field coordinate zero and polynomial coordinate `X`. -/
theorem x_spec (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (pullbackSituation k k').bprimeToB (x k k') = 0 ∧
      (pullbackSituation k k').bprimeToAprime (x k k') = Polynomial.X := sorry

/-- Membership in the distinguished ideal is exactly vanishing at the origin in the polynomial chart. -/
theorem distinguishedIdeal_spec (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (z : coefficientRing k k') :
    z ∈ distinguishedIdeal k k' ↔
      Polynomial.eval (0 : k') ((pullbackSituation k k').bprimeToAprime z) = 0 := sorry

/-- Under the polynomial presentation, the distinguished ideal is the intersection with `(X)`. -/
theorem distinguishedIdeal_subring_mem_iff (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (z : coefficientRing k k') :
    z ∈ distinguishedIdeal k k' ↔
      (coefficientRing_toSubring k k' z).1 ∈
        (Ideal.span {Polynomial.X} : Ideal (Polynomial k')) := sorry

/-- The distinguished ideal is maximal in the coefficient ring. -/
@[instance]
theorem distinguishedIdeal_isMaximal (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    (distinguishedIdeal k k').IsMaximal := sorry

/-- A nontrivial finite extension identifies the two principal localizations, carrying the inverse
of `x` to the coordinate `y`. -/
theorem exists_localizationIso
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    (h_nontrivial : ¬ Function.Surjective (algebraMap k k')) :
    ∃ e : CommRingCat.of (Localization.Away (x k k')) ≅
        CommRingCat.of (Localization.Away (y k')),
      e.hom.hom (IsLocalization.Away.invSelf (x k k')) =
        algebraMap (Polynomial k') (Localization.Away (y k')) (y k') := sorry

/-- The affine chart map from the coefficient ring to the ground-field spectrum. -/
def coefficientChartBase (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Spec (CommRingCat.of (coefficientRing k k')) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (coefficientBaseMap k k'))

/-- The affine chart map from the polynomial ring to the ground-field spectrum. -/
def polynomialChartBase (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    Spec (CommRingCat.of (Polynomial k')) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom
    ((Polynomial.C : k' →+* Polynomial k').comp (algebraMap k k')))

/-- The overlap scheme obtained by localizing the coefficient chart at `x`. -/
abbrev overlapScheme (k k' : Type u) [Field k] [Field k'] [Algebra k k'] : Scheme :=
  Spec (CommRingCat.of (Localization.Away (x k k')))

/-- The overlap map from the localized coefficient chart to the coefficient chart. -/
def overlapToCoefficient (k k' : Type u) [Field k] [Field k'] [Algebra k k'] :
    overlapScheme k k' ⟶ Spec (CommRingCat.of (coefficientRing k k')) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (coefficientRing k k') (Localization.Away (x k k'))))

/-- The overlap map to the polynomial chart, transported through a chosen localization equivalence. -/
def overlapToPolynomial
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (e : CommRingCat.of (Localization.Away (x k k')) ≅
      CommRingCat.of (Localization.Away (y k'))) :
    overlapScheme k k' ⟶ Spec (CommRingCat.of (Polynomial k')) :=
  Spec.map e.inv ≫ Spec.map (CommRingCat.ofHom
    (algebraMap (Polynomial k') (Localization.Away (y k'))))

/-- A finite extension yields a proper singular curve with the two affine charts, global sections
equal to the ground field, and normalization the projective line over the extension field. -/
theorem exists_gluedCurve
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    (h_nontrivial : ¬ Function.Surjective (algebraMap k k')) :
    ∃ e : CommRingCat.of (Localization.Away (x k k')) ≅
        CommRingCat.of (Localization.Away (y k')),
      ∃ h_e : e.hom.hom (IsLocalization.Away.invSelf (x k k')) =
        algebraMap (Polynomial k') (Localization.Away (y k')) (y k'),
      ∃ X : SchemeOverField k,
        ∃ h_curve : Curve X,
        ∃ h_proper : IsProper X.hom,
        ∃ hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom),
        ∃ (a : Spec (CommRingCat.of (coefficientRing k k')) ⟶ X.left)
          (b : Spec (CommRingCat.of (Polynomial k')) ⟶ X.left),
          ∃ h_a_base : coefficientChartBase k k' = a ≫ X.hom,
          ∃ h_b_base : polynomialChartBase k k' = b ≫ X.hom,
          ∃ h_a_open : IsOpenImmersion a,
          ∃ h_b_open : IsOpenImmersion b,
          ∃ h_pushout : IsPushout
            (overlapToCoefficient k k') (overlapToPolynomial k k' e) a b,
          ∃ (p : SchemeOverField.point k ⟶ X)
            (q : PrimeSpectrum (coefficientRing k k')),
            ∃ h_qideal : q.asIdeal = distinguishedIdeal k k',
            ∃ h_qpoint : a.base q =
              SchemeOverField.rationalPoint p (IsLocalRing.closedPoint k),
            ∃ h_singular : ¬ IsRegularLocalRing
              (SchemeOverField.stalkRing X
                (SchemeOverField.rationalPoint p (IsLocalRing.closedPoint k))),
            ∃ h_maximal : (distinguishedIdeal k k').IsMaximal,
            ∃ X' : SchemeOverField k',
              ∃ ν : X'.left ⟶ X.left,
                ∃ e_projectiveLine : X' ≅ ProjectiveSpace.schemeOver k' 1,
                ∃ h_finite : IsFinite ν,
                ∃ h_birational : IsBirational ν,
                ∃ h_regular : Scheme.Regular X'.left,
                  X'.hom ≫ FieldExtension.specMap k k' = ν ≫ X.hom := sorry

end AlgebraicGeometry.FiniteExtensionCurve

end
