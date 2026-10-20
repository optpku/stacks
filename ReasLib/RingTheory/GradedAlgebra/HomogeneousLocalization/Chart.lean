module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Algebra.Algebra.Tower
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Algebra
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Algebra charts for homogeneous localization

This leaf owns only the algebra-side chart data.  The neutral homogeneous-localization `Algebra`
leaf supplies the canonical base-algebra and scalar-tower instances; module comparisons and
finiteness conditions belong to the module-enriched `Model` leaf.
-/

noncomputable section

universe u u' ui us

namespace HomogeneousLocalization

/-- A graded algebra chart whose chosen homogeneous localization models an algebra `R'`.

The carrier, grading, denominator, and comparison equivalences are concrete fields.  The
typeclass fields record the chosen algebraic structures.  Derived operations install those
structures at their own boundary, rather than registering a noncanonical chart as a global
instance owner.
-/
@[stacks 052N "graded homogeneous-localization algebra chart"]
structure AlgebraChart
    {R : Type u} {R' : Type u'}
    [CommRing R] [CommSemiring R'] [Algebra R R']
    {ι : Type ui} [AddCommMonoid ι] [DecidableEq ι] {d : ι} where
  /-- The graded ambient commutative ring. -/
  S : Type us
  /-- The commutative-ring structure on the ambient ring. -/
  [commRing : CommRing S]
  /-- The base-algebra structure on the ambient ring. -/
  [algebra : Algebra R S]
  /-- The grading of the ambient ring. -/
  grading : ι → Submodule R S
  /-- The graded-algebra laws for `grading`. -/
  [gradedAlgebra : GradedAlgebra grading]
  /-- The chosen homogeneous denominator. -/
  f : grading d
  /-- The degree-zero component identified with the original base ring. -/
  zeroEquiv : R ≃ₐ[R] grading 0
  /-- The away chart identified with the target algebra. -/
  awayEquiv : R' ≃ₐ[R]
    HomogeneousLocalization.Away grading (f : S)

namespace AlgebraChart

variable {R : Type u} {R' : Type u'}
variable [CommRing R] [CommSemiring R'] [Algebra R R']
variable {ι : Type ui} [AddCommMonoid ι] [DecidableEq ι] {d : ι}
variable (chart : AlgebraChart (R := R) (R' := R') (ι := ι) (d := d))

/- The chart is an explicit data bundle.  Its stored structures are installed only inside the
  operations below; registering them globally would make a noncanonical chart an ambient owner. -/

/-- The homogeneous away ring carried by an algebra chart.

This is a transparent alias for Mathlib's canonical away carrier.  Keeping the raw carrier at the
public boundary means the generic `HomogeneousLocalization.Away` API applies without casts. -/
@[stacks 07Z2 "algebra chart away ring"]
noncomputable abbrev awayRing : Type _ :=
  -- Local instance justification (defeq pin): expose the structures stored by this explicit chart
  -- without making a noncanonical chart a global typeclass owner.
  let _ := chart.commRing
  let _ := chart.algebra
  let _ := chart.gradedAlgebra
  HomogeneousLocalization.Away chart.grading (chart.f : chart.S)

/-- The `R'`-algebra induced by the chart's algebra equivalence. -/
@[reducible, stacks 07Z2 "algebra chart away algebra"]
noncomputable def awayAlgebra :
    -- Local instance justification (noncanonical chart data): the algebra is induced by this
    -- chart's selected commutative ring, base algebra, and grading.
    letI := chart.commRing
    letI := chart.algebra
    letI := chart.gradedAlgebra
    letI : CommRing (HomogeneousLocalization.Away chart.grading (chart.f : chart.S)) :=
      HomogeneousLocalization.homogeneousLocalizationCommRing
    Algebra R' (HomogeneousLocalization.Away chart.grading (chart.f : chart.S)) :=
by
  letI := chart.commRing
  letI := chart.algebra
  letI := chart.gradedAlgebra
  letI : CommRing (HomogeneousLocalization.Away chart.grading (chart.f : chart.S)) :=
    HomogeneousLocalization.homogeneousLocalizationCommRing
  exact chart.awayEquiv.toRingEquiv.toRingHom.toAlgebra

/-- The base/target/away scalar tower induced by the chart. -/
@[stacks 07Z2 "algebra chart away scalar tower"]
theorem awayTower :
    -- Local instance justification (noncanonical chart data): the tower is transported only for
    -- this explicit chart value, rather than registered for every chart.
    letI := chart.commRing
    letI := chart.algebra
    letI := chart.gradedAlgebra
    letI : CommRing (HomogeneousLocalization.Away chart.grading (chart.f : chart.S)) :=
      HomogeneousLocalization.homogeneousLocalizationCommRing
    letI : Algebra R' (HomogeneousLocalization.Away chart.grading (chart.f : chart.S)) :=
      chart.awayAlgebra
    IsScalarTower R R' (HomogeneousLocalization.Away chart.grading (chart.f : chart.S)) := sorry

end AlgebraChart

end HomogeneousLocalization
