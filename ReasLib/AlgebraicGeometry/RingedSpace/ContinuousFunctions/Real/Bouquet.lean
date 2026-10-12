/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.ContinuousFunctions.Real.Sections
public import ReasLib.Topology.MetricSpace.RealBouquet
import Mathlib.Tactic.CrossRefAttribute

/-!
# Branch-supported sections on real bouquets

A continuous function on one real branch, normalized by its value at the origin, defines a
structure-module section supported on that branch.  Uniform local constancy near the common origin
makes the resulting family of section supports locally finite.
-/

@[expose] public section

open TopologicalSpace
open scoped Topology

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ContinuousFunctions.Real.Bouquet

variable {ι : Type u}

/-- A continuous real function normalized and supported on one branch, viewed as a section of the
continuous-function structure module. -/
@[stacks 01BL "branch-supported coefficient section"]
noncomputable def supportedSection (i : ι) (f : C(ℝ, ℝ)) :
    (SheafOfModules.unit
      (ringedSpace (TopCat.of (Metric.RealBouquet ι))).ringCatSheaf).sections :=
  unitSection (TopCat.of (Metric.RealBouquet ι)) (Metric.RealBouquet.supportedOn i f)

/-- Evaluation of a branch-supported coefficient section is the corresponding branch-supported
continuous function. -/
@[simp, stacks 01BL "branch-supported coefficient evaluation"]
theorem sectionValue_supportedSection (i : ι) (f : C(ℝ, ℝ))
    (U : Opens (TopCat.of (Metric.RealBouquet ι))) (x : U) :
    sectionValue (TopCat.of (Metric.RealBouquet ι)) (supportedSection i f) U x =
      Metric.RealBouquet.supportedOn i f x.1 := sorry

/-- Branch-supported coefficient sections are locally finite when their defining functions are
uniformly constant near the common origin. -/
@[stacks 01BL "locally finite branch-supported sections"]
theorem locallyFinite_supportedSection
    (f : ι → C(ℝ, ℝ)) {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ i x, |x| < ε → f i x = f i 0) :
    LocallyFinite fun i ↦ SheafOfModules.sectionSupport (supportedSection i (f i)) := sorry

end AlgebraicGeometry.RingedSpace.ContinuousFunctions.Real.Bouquet
