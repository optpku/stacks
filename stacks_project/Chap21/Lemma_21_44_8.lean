/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocalRepresentation
import StacksCheckRecall

@[expose] public section

/- Lemma 21.44.8 (1) (08FR): a derived morphism from a strictly perfect complex is locally
represented by chain maps. -/
@[stacks 08FR "(1)"]
#check @RingedSite.CochainComplex.IsStrictlyPerfect.locallyRepresentedAt

/- Lemma 21.44.8 (2) (08FR): a chain map from a strictly perfect complex which vanishes in the
derived category is locally null-homotopic. -/
@[stacks 08FR "(2)"]
#check @RingedSite.CochainComplex.IsStrictlyPerfect.locallyNullHomotopicAt
