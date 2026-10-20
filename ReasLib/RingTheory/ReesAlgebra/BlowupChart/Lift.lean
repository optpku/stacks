module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.RingTheory.Ideal.Principal
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.ChartMap

/-!
# Maps from affine blowup charts to discrete valuation rings

An affine blowup chart `R[I / a]` maps canonically to a discrete valuation ring `B`
whenever a ring map `f : R →+* B` sends `a` to a nonzero element dividing the
image of every element of `I`.  On a homogeneous fraction of degree `n`, the
map takes the canonical DVR quotient of its evaluated numerator by its evaluated
denominator.
-/

@[expose] public section

noncomputable section

open HomogeneousLocalization
open scoped AffineBlowupChart

universe u v

namespace AffineBlowupChart

variable {R : Type u} [CommRing R]
variable {B : Type v} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

/-- Compatible center data whose distinguished parameter has nonzero image in a target discrete
valuation ring. -/
@[stacks 052Q "affine blowup chart DVR map"]
structure ChartMap.DVR (I : Ideal R) (a : I) extends ChartMap (B := B) I a where
  /-- The image of the distinguished chart parameter is nonzero. -/
  parameter_ne_zero : toChartMap.toRingHom a.1 ≠ 0

/-- Evaluation at `t = 1` of the Rees algebra, followed by a ring map `R →+* B`. -/
def reesEval (I : Ideal R) (f : R →+* B) : reesAlgebra I →+* B :=
  (Polynomial.eval₂RingHom f 1).comp (reesAlgebra I).toSubring.subtype

namespace ChartMap

namespace DVR

/-- Build DVR chart data from the ideal-theoretic form of its center containment condition. -/
@[stacks 052Q "DVR chart map from center containment"]
def ofMapCenterLe {I : Ideal R} {a : I} (f : R →+* B)
    (parameter_ne_zero : f a.1 ≠ 0)
    (map_center_le : Ideal.map f I ≤ Ideal.span {f a.1}) : DVR (B := B) I a where
  toChartMap := ChartMap.ofMapCenterLe f map_center_le
  parameter_ne_zero := parameter_ne_zero

/-- Build DVR chart data from pointwise divisibility of the image of every center element by the
parameter image. -/
@[stacks 052Q "DVR chart map from center divisibility"]
def ofDvd {I : Ideal R} {a : I} (f : R →+* B)
    (parameter_ne_zero : f a.1 ≠ 0)
    (parameter_dvd : ∀ x : I, f a.1 ∣ f x.1) : DVR (B := B) I a where
  toChartMap := ChartMap.ofDvd f parameter_dvd
  parameter_ne_zero := parameter_ne_zero

/-- The value in the target DVR of a same-degree homogeneous fraction before passing to the
quotient. -/
def quotientValue {I : Ideal R} {a : I} (g : DVR (B := B) I a)
    (x : HomogeneousLocalization.NumDenSameDeg (ReesAlgebra.Grading.grade I)
      (Submonoid.powers (ReesAlgebra.Grading.degreeOne I a))) : B :=
  IsDiscreteValuationRing.quotient
    (reesEval I g.toChartMap.toRingHom x.num) (reesEval I g.toChartMap.toRingHom x.den)

/-- Equal homogeneous fractions have equal evaluated DVR quotient values. -/
theorem quotientValue_eq_of_embedding_eq {I : Ideal R} {a : I} (g : DVR (B := B) I a)
    (x y : HomogeneousLocalization.NumDenSameDeg (ReesAlgebra.Grading.grade I)
      (Submonoid.powers (ReesAlgebra.Grading.degreeOne I a)))
    (hxy : x.embedding = y.embedding) :
    quotientValue g x = quotientValue g y := sorry

/-- The underlying function of the chart lift associated to a DVR chart map. -/
noncomputable def liftFun {I : Ideal R} {a : I} (g : DVR (B := B) I a) : R[I / a] → B :=
  fun z ↦ Quotient.liftOn' z (quotientValue g)
    (fun x y hxy ↦ quotientValue_eq_of_embedding_eq g x y hxy)

/-- The chart-lift function preserves zero. -/
theorem liftFun_zero {I : Ideal R} {a : I} (g : DVR (B := B) I a) :
    liftFun g 0 = 0 := sorry

/-- The chart-lift function preserves one. -/
theorem liftFun_one {I : Ideal R} {a : I} (g : DVR (B := B) I a) :
    liftFun g 1 = 1 := sorry

/-- The chart-lift function preserves addition. -/
theorem liftFun_add {I : Ideal R} {a : I} (g : DVR (B := B) I a) (x y : R[I / a]) :
    liftFun g (x + y) = liftFun g x + liftFun g y := sorry

/-- The chart-lift function preserves multiplication. -/
theorem liftFun_mul {I : Ideal R} {a : I} (g : DVR (B := B) I a) (x y : R[I / a]) :
    liftFun g (x * y) = liftFun g x * liftFun g y := sorry

/-- The canonical ring map from an affine blowup chart to the target discrete valuation ring. -/
@[stacks 052Q "affine blowup chart DVR lift"]
noncomputable def lift {I : Ideal R} {a : I} (g : DVR (B := B) I a) : R[I / a] →+* B where
  toFun := liftFun g
  map_one' := liftFun_one g
  map_mul' := liftFun_mul g
  map_zero' := liftFun_zero g
  map_add' := liftFun_add g

/-- On the base ring, the chart lift agrees with the underlying map of its DVR chart map. -/
@[stacks 052Q "affine blowup chart DVR lift on scalars", simp]
theorem lift_algebraMap {I : Ideal R} {a : I} (g : DVR (B := B) I a) (r : R) :
    lift g (@algebraMap R R[I / a] _ _ (AffineBlowupChart.instAlgebra I a) r) =
      g.toChartMap.toRingHom r := sorry

/-- The chart lift sends the basic fraction `x / a` to the DVR quotient of its mapped numerator
by its mapped parameter. -/
@[stacks 052Q "affine blowup chart DVR lift on basic fraction", simp]
theorem lift_basicFraction {I : Ideal R} {a x : I} (g : DVR (B := B) I a) :
    lift g (AffineBlowupChart.basicFraction I a x) =
      IsDiscreteValuationRing.quotient (g.toChartMap.toRingHom x.1)
        (g.toChartMap.toRingHom a.1) := sorry

/-- The chart lift sends a normalized power fraction to the corresponding quotient of mapped
numerator and parameter power. -/
@[stacks 052Q "affine blowup chart DVR lift on power fraction", simp]
theorem lift_powerFraction {I : Ideal R} {a : I} (g : DVR (B := B) I a)
    (n : ℕ) (r : ↥(I ^ n)) :
    lift g (AffineBlowupChart.powerFraction I a n r) =
      IsDiscreteValuationRing.quotient (g.toChartMap.toRingHom r.1)
        ((g.toChartMap.toRingHom a.1) ^ n) := sorry

end DVR

end ChartMap

end AffineBlowupChart
