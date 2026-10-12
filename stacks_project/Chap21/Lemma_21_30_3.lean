/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.InjectiveResolution
public import ReasLib.CategoryTheory.Sites.Over.Derived
public import ReasLib.CategoryTheory.Sites.TopologyComparison.HigherDirectImage

@[expose] public section

/-!
# Lemma 21.30.3

Recall facade for the reusable topology-comparison higher-direct-image API.  The source-facing
comparison uses the continuous slice presentation, while
`Derived.Over.pushforwardDegree` and its presentation bridge remain reusable cocontinuous views.
The bounded-below canonical map is `Derived.Plus.pushforwardComparisonOf`; `(V_n)` enters only
the degreewise statements owned by `TopologyComparison.HigherDirectImage`.
-/

open CategoryTheory CategoryTheory.GrothendieckTopology
open scoped CategoryTheory.GrothendieckTopology

/- Lemma 21.30.3 (0EZA), canonical bounded-below direct-image comparison. -/
@[stacks 0EZA "canonical bounded-below direct-image comparison"]
#check @Derived.Plus.pushforwardComparisonOf

/- The canonical homology projection of the bounded-below comparison is kept separate from the
ordinary `rightDerived` degree presentation used by the source-facing bridge below. -/
@[stacks 0EZA "homology component of the direct-image comparison"]
#check @Derived.Plus.pushforwardComparisonHomologyApp

@[stacks 0EZA "explicit-pullback homology component of the direct-image comparison"]
#check @Derived.Plus.pushforwardComparisonHomologyAppOf
#check @Functor.RightDerived.Bounded.degree.degreeFunctorIsoRightDerived

@[stacks 0EZA "direct-image comparison mate specification"]
#check @Derived.Plus.pushforwardComparison_mate

/- The following is a supporting vanishing bridge.  It is not a second source-facing map; the
   canonical morphism remains `Derived.Plus.pushforwardComparisonHomologyAppOf`. -/
#check @TopologyComparison.HigherDirectImage.comparisonPushforward_isZero

/- The proposition-level statement is retained as a source-compatible view.  Downstream code should
   use the canonical homology component together with its `IsIso` certificate below. -/
@[stacks 0EZA "source-compatible proposition view"]
#check @TopologyComparison.HigherDirectImage.comparison_isomorphic

/- The cocontinuous slice presentation is a separate compatibility view; its pointwise right-Kan
   hypotheses are exposed by the owner rather than hidden in a chapter-local instance. -/
@[stacks 0EZA "cocontinuous presentation compatibility"]
#check @TopologyComparison.HigherDirectImage.comparison_isomorphic_cocontinuous

/- The canonical bounded-below homology arrow and its `(V_n)` invertibility certificate. -/
@[stacks 0EZA "canonical homology component is invertible under (V_n)"]
#check @TopologyComparison.HigherDirectImage.comparison_homology_isIso

/- Canonical slice-site degree owner used by both source-facing statements. -/
#check @Derived.Over.pushforwardDegree
#check @Derived.Over.pushforwardDegreeContinuous
#check @Derived.Over.pushforwardDegreeContinuousOf
#check @Derived.Over.pushforwardDegreePresentationIso

end
