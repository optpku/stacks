/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ClosedPoint
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SheafOfModules
open scoped AlgebraicGeometry nonZeroDivisors

universe u

/- Lemma 33.43.8 (1): at a closed point of a curve over a field, regularity and
normality of the local ring, the discrete valuation ring condition, invertibility
of the reduced point's defining ideal sheaf, and the effective-Cartier condition
are equivalent. -/
@[stacks 0B8Y] #check
  (AlgebraicGeometry.Curve.ClosedPoint.regularity_tfae :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X]
      (x : X.left) (hx : x ∈ closedPoints X.left),
      let Y := X.left
      let D : Y.IdealSheafData :=
        Scheme.IdealSheafData.vanishingIdeal
          ⟨({x} : Set Y), by simpa [closedPoints] using hx⟩
      let F := Y.presheaf
      let ℐ : Y.Modules :=
        kernel (unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom)
      List.TFAE
        [ IsRegularLocalRing (F.stalk x),
          IsNormalRing (F.stalk x),
          IsDiscreteValuationRing (F.stalk x),
          Scheme.Modules.Invertible ℐ,
          AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι ])

/- Lemma 33.43.8 (2): under perfectness of the base field or separability of
the residue-field extension, those five conditions are also equivalent to
smoothness at the closed point. -/
@[stacks 0B8Y] #check
  (AlgebraicGeometry.Curve.ClosedPoint.regularity_smoothAt_tfae :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X]
      (x : X.left) (hx : x ∈ closedPoints X.left),
      (PerfectField k ∨ Algebra.IsSeparable k (X.left.residueField x)) →
      let Y := X.left
      let D : Y.IdealSheafData :=
        Scheme.IdealSheafData.vanishingIdeal
          ⟨({x} : Set Y), by simpa [closedPoints] using hx⟩
      let F := Y.presheaf
      let ℐ : Y.Modules :=
        kernel (unitToPushforwardObjUnit D.subschemeι.toRingCatSheafHom)
      List.TFAE
        [ IsRegularLocalRing (F.stalk x),
          IsNormalRing (F.stalk x),
          IsDiscreteValuationRing (F.stalk x),
          Scheme.Modules.Invertible ℐ,
          AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι,
          X.hom.SmoothAt x ])
