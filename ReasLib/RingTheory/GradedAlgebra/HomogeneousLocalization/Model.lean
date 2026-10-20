module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.FiniteType
public import ReasLib.Algebra.Module.Equiv.Semilinear
public import ReasLib.Algebra.Module.Graded.Left
public import ReasLib.Algebra.Module.Graded.Finite
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy
public import ReasLib.RingTheory.GradedAlgebra.DegreeZero
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Away.Module
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Away.Scalar
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Finite
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Chart
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Graded homogeneous-localization models

This leaf packages the data carried by the final finite-module construction in a reusable form.
The carriers, actions, gradings, and comparison equivalences are fields of `Model`; the finiteness
conditions and the optional generation condition are named propositions.  The module chart is
delegated to `GradedModule.Left`, so downstream code sees the same carrier and instance API as any
other graded module.  Keeping the conditions separate lets a consumer use the finite module
consequences without carrying a generation hypothesis, while `Model.Spec` remains the bundled
source-facing specification.
-/

noncomputable section

universe u u' v un ui us

namespace HomogeneousLocalization

/-- A graded algebra/module chart whose localization at a chosen homogeneous element models an
algebra and a module.

The bundle deliberately stores the actual carriers and comparison equivalences rather than an
existential witness hidden behind `Nonempty`.  The algebra side is a single `AlgebraChart` parent;
the module side adds only the graded module and its semilinear comparison.  Stored structures are
kept explicit and are installed locally by operations that need them, since a chart is a chosen
data object rather than a global typeclass owner. -/
@[stacks 052N "graded homogeneous-localization model"]
structure Model
    {R : Type u} {R' : Type u'} {M : Type v}
    [CommRing R] [CommSemiring R'] [Algebra R R']
    [AddCommMonoid M] [Module R' M]
    {ι : Type ui} [AddCommMonoid ι] [DecidableEq ι] {d : ι} where
  /-- The single algebra-side chart owned by the model. -/
  toAlgebraChart : AlgebraChart (R := R) (R' := R') (ι := ι) (d := d)
  /-- The graded module chart over the ambient graded algebra.

  This reuses `GradedModule.Left`, so the carrier, scalar actions, decomposition, and graded
  scalar multiplication are owned by the shared graded-module API rather than duplicated here.
  The `let _` binders make the parent chart's chosen algebraic structures explicit in the field
  type without registering a model-dependent global instance. -/
  gradedModule :
    let _ := toAlgebraChart.commRing
    let _ := toAlgebraChart.algebra
    let _ := toAlgebraChart.gradedAlgebra
    GradedModule.Left.{ui, un, us, u} toAlgebraChart.grading
  /-- The localized degree-zero module identified with the original module. -/
  moduleEquiv :
    let _ := toAlgebraChart.commRing
    let _ := toAlgebraChart.algebra
    let _ := toAlgebraChart.gradedAlgebra
    let _ := RingHomInvPair.of_ringEquiv toAlgebraChart.awayEquiv.toRingEquiv
    let _ := RingHomInvPair.of_ringEquiv_symm toAlgebraChart.awayEquiv.toRingEquiv
    M ≃ₛₗ[(toAlgebraChart.awayEquiv.toRingEquiv : R' →+*
      HomogeneousLocalization.Away toAlgebraChart.grading
        (toAlgebraChart.f : toAlgebraChart.S))]
      HomogeneousLocalization.Away.Module.degreeZeroPart
        toAlgebraChart.grading gradedModule.grading toAlgebraChart.f

namespace Model

variable {R : Type u} {R' : Type u'} {M : Type v}
variable [CommRing R] [CommSemiring R'] [Algebra R R']
variable [AddCommMonoid M] [Module R' M]
variable {ι : Type ui} [AddCommMonoid ι] [DecidableEq ι] {d : ι}

/-- Construct a localization model from an explicit algebra chart, graded module, and comparison.

The constructor keeps the dependent chart instances at the boundary where they are chosen.  This
is the reusable smart constructor; `Model.mk` remains available for code that already has the
dependent fields in exactly the structure's native form. -/
@[stacks 052N "graded homogeneous-localization model constructor"]
def of
    (chart : AlgebraChart (R := R) (R' := R') (ι := ι) (d := d))
    (gradedModule :
      let _ := chart.commRing
      let _ := chart.algebra
      let _ := chart.gradedAlgebra
      GradedModule.Left chart.grading)
    (moduleEquiv :
      let _ := chart.commRing
      let _ := chart.algebra
      let _ := chart.gradedAlgebra
      let _ := RingHomInvPair.of_ringEquiv chart.awayEquiv.toRingEquiv
      let _ := RingHomInvPair.of_ringEquiv_symm chart.awayEquiv.toRingEquiv
      M ≃ₛₗ[(chart.awayEquiv.toRingEquiv : R' →+*
        HomogeneousLocalization.Away chart.grading (chart.f : chart.S))]
        HomogeneousLocalization.Away.Module.degreeZeroPart
          chart.grading gradedModule.grading chart.f) :
    Model (R := R) (R' := R') (M := M) (ι := ι) (d := d) :=
  { toAlgebraChart := chart
    gradedModule := gradedModule
    moduleEquiv := moduleEquiv }

end Model

namespace Model

variable {R : Type u} {R' : Type u'} {M : Type v}
variable [CommRing R] [CommSemiring R'] [Algebra R R']
variable [AddCommMonoid M] [Module R' M]
variable {ι : Type ui} [AddCommMonoid ι] [DecidableEq ι] {d : ι}
variable (model : Model (R := R) (R' := R') (M := M) (ι := ι) (d := d))

/- The neutral finiteness predicate is named at the model boundary so consumers do not have to
  repeat the chosen chart and graded-module instance pins.  Its mathematical payload remains the
  reusable `GradedModule.FiniteSpec` structure. -/
/-- The finite-type and finite-module conditions carried by a localization model. -/
@[stacks 052N "finite graded localization model predicate"]
def finiteSpec : Prop :=
  let _ := model.toAlgebraChart.commRing
  let _ := model.toAlgebraChart.algebra
  let _ := model.toAlgebraChart.gradedAlgebra
  let _ := model.gradedModule.addCommMonoid
  let _ := model.gradedModule.moduleBase
  let _ := model.gradedModule.moduleAlgebra
  let _ := model.gradedModule.isScalarTower
  let _ := model.gradedModule.decomposition
  let _ := model.gradedModule.gradedSMul
  Algebra.FiniteType R model.toAlgebraChart.S ∧
    Module.Finite model.toAlgebraChart.S model.gradedModule

/- The degree-zero module below is the first genuinely model-specific carrier: it combines the
  chart's denominator with the chosen graded module.  All ambient chart projections remain available
  through `model.toAlgebraChart`, so no duplicate aliases are needed. -/
/-- The degree-zero module in the away chart carried by a model. -/
@[stacks 052N "model away module"]
noncomputable abbrev awayModule : Type _ :=
  -- The degree-zero construction consumes the model's chosen graded-module projections; they are
  -- intentionally local because another model may carry a different action on the same carrier.
  let _ := model.toAlgebraChart.commRing
  let _ := model.toAlgebraChart.algebra
  let _ := model.toAlgebraChart.gradedAlgebra
  let _ := model.gradedModule.addCommMonoid
  let _ := model.gradedModule.moduleBase
  let _ := model.gradedModule.moduleAlgebra
  let _ := model.gradedModule.isScalarTower
  let _ := model.gradedModule.decomposition
  let _ := model.gradedModule.gradedSMul
  HomogeneousLocalization.Away.Module.degreeZeroPart
    model.toAlgebraChart.grading model.gradedModule.grading model.toAlgebraChart.f

/- The target action is pulled back along the selected ring equivalence, rather than inferred from
  an arbitrary ambient `Algebra R'` instance. -/

/-- The pulled-back `R'`-module structure on the localized degree-zero module. -/
@[reducible, stacks 07Z2 "model away module structure"]
noncomputable def awayModuleStructure :
    -- This is the one noncanonical scalar choice that downstream linear APIs may opt into.
    let _ := model.toAlgebraChart.commRing
    let _ := model.toAlgebraChart.algebra
    let _ := model.toAlgebraChart.gradedAlgebra
    let _ := model.gradedModule.addCommMonoid
    let _ := model.gradedModule.moduleBase
    let _ := model.gradedModule.moduleAlgebra
    let _ := model.gradedModule.isScalarTower
    let _ := model.gradedModule.decomposition
    let _ := model.gradedModule.gradedSMul
    Module R' model.awayModule :=
by
  letI := model.toAlgebraChart.commRing
  letI := model.toAlgebraChart.algebra
  letI := model.toAlgebraChart.gradedAlgebra
  letI := model.gradedModule.addCommMonoid
  letI := model.gradedModule.moduleBase
  letI := model.gradedModule.moduleAlgebra
  letI := model.gradedModule.isScalarTower
  letI := model.gradedModule.decomposition
  letI := model.gradedModule.gradedSMul
  letI : CommRing (HomogeneousLocalization.Away model.toAlgebraChart.grading
      (model.toAlgebraChart.f : model.toAlgebraChart.S)) :=
    HomogeneousLocalization.homogeneousLocalizationCommRing
  exact Module.compHom model.awayModule
    (model.toAlgebraChart.awayEquiv.toRingEquiv : R' →+*
      model.toAlgebraChart.awayRing)

/-- View the localized module comparison as an ordinary `R'`-linear equivalence.  The shared
semilinear bridge supplies the pulled-back action.  The `let _` is part of the named API because
the action is a model-specific choice, not a canonical instance on the raw degree-zero carrier. -/
@[stacks 052N "model localized module linear equivalence"]
noncomputable def moduleEquivLinear :
    let _ := model.toAlgebraChart.commRing
    let _ := model.toAlgebraChart.algebra
    let _ := model.toAlgebraChart.gradedAlgebra
    let _ := model.gradedModule.addCommMonoid
    let _ := model.gradedModule.moduleBase
    let _ := model.gradedModule.moduleAlgebra
    let _ := model.gradedModule.isScalarTower
    let _ := model.gradedModule.decomposition
    let _ := model.gradedModule.gradedSMul
    let _ := RingHomInvPair.of_ringEquiv model.toAlgebraChart.awayEquiv.toRingEquiv
    let _ := RingHomInvPair.of_ringEquiv_symm model.toAlgebraChart.awayEquiv.toRingEquiv
    let _ : Module R' model.awayModule := model.awayModuleStructure
    M ≃ₗ[R'] model.awayModule :=
by
  letI := model.toAlgebraChart.commRing
  letI := model.toAlgebraChart.algebra
  letI := model.toAlgebraChart.gradedAlgebra
  letI := model.gradedModule.addCommMonoid
  letI := model.gradedModule.moduleBase
  letI := model.gradedModule.moduleAlgebra
  letI := model.gradedModule.isScalarTower
  letI := model.gradedModule.decomposition
  letI := model.gradedModule.gradedSMul
  letI := RingHomInvPair.of_ringEquiv model.toAlgebraChart.awayEquiv.toRingEquiv
  letI := RingHomInvPair.of_ringEquiv_symm model.toAlgebraChart.awayEquiv.toRingEquiv
  letI : Module R' model.awayModule := model.awayModuleStructure
  exact LinearEquiv.ofSemilinear model.toAlgebraChart.awayEquiv.toRingEquiv model.moduleEquiv

/-- The linearized module comparison has the same underlying function as the stored comparison. -/
@[simp, stacks 052N "model localized module linear equivalence application"]
theorem moduleEquivLinear_apply (x : M) :
    let _ := model.toAlgebraChart.commRing
    let _ := model.toAlgebraChart.algebra
    let _ := model.toAlgebraChart.gradedAlgebra
    let _ := model.gradedModule.addCommMonoid
    let _ := model.gradedModule.moduleBase
    let _ := model.gradedModule.moduleAlgebra
    let _ := model.gradedModule.isScalarTower
    let _ := model.gradedModule.decomposition
    let _ := model.gradedModule.gradedSMul
    let _ := RingHomInvPair.of_ringEquiv model.toAlgebraChart.awayEquiv.toRingEquiv
    let _ := RingHomInvPair.of_ringEquiv_symm model.toAlgebraChart.awayEquiv.toRingEquiv
    let _ : Module R' model.awayModule := model.awayModuleStructure
    model.moduleEquivLinear x = model.moduleEquiv x := sorry

/-- The full source-facing specification, extending the finite consequences with generation by the
  chosen homogeneous piece. -/
@[stacks 052N "finite graded localization model specification"]
structure Spec : Prop where
  /-- The neutral finiteness specification for the graded algebra/module pair. -/
  finite : model.finiteSpec
  /-- The ambient graded algebra is generated over degree zero by the chosen degree-`d` piece. -/
  generatedBy :
    let _ := model.toAlgebraChart.commRing
    let _ := model.toAlgebraChart.algebra
    let _ := model.toAlgebraChart.gradedAlgebra
    GradedAlgebra.GeneratedBy model.toAlgebraChart.grading d

/-- Construct the source-facing specification from its independent finiteness and generation
conditions.  The named `finiteSpec` owner keeps the dependent instance choices out of consumer
call sites while the generation hypothesis remains separate. -/
@[stacks 052N "finite graded localization specification constructor"]
theorem Spec.of
    (hfinite : model.finiteSpec)
    (hgeneratedBy :
      let _ := model.toAlgebraChart.commRing
      let _ := model.toAlgebraChart.algebra
      let _ := model.toAlgebraChart.gradedAlgebra
      GradedAlgebra.GeneratedBy model.toAlgebraChart.grading d) :
    model.Spec := sorry

/-- The source-facing specification is exactly its independent finiteness and generation data. -/
@[stacks 052N "finite graded localization specification iff"]
theorem Spec.iff :
    model.Spec ↔
      model.finiteSpec ∧
        (let _ := model.toAlgebraChart.commRing
         let _ := model.toAlgebraChart.algebra
         let _ := model.toAlgebraChart.gradedAlgebra
         GradedAlgebra.GeneratedBy model.toAlgebraChart.grading d) := sorry

/-- The degree-zero module in a finite model is finite over its away-localized ring. -/
@[stacks 052N "model finite away module"]
theorem finiteAwayModule
    (hmodel : model.finiteSpec) :
    let _ := model.toAlgebraChart.commRing
    let _ := model.toAlgebraChart.algebra
    let _ := model.toAlgebraChart.gradedAlgebra
    let _ := model.gradedModule.addCommMonoid
    let _ := model.gradedModule.moduleBase
    let _ := model.gradedModule.moduleAlgebra
    let _ := model.gradedModule.isScalarTower
    let _ := model.gradedModule.decomposition
    let _ := model.gradedModule.gradedSMul
    Module.Finite model.toAlgebraChart.awayRing model.awayModule := sorry

end Model

end HomogeneousLocalization
