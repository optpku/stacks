/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.MayerVietoris
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.29.2

The reusable bounded-below essential-image criterion is owned by the topology-comparison
Mayer--Vietoris leaf. Its statement keeps the sheaf-detection hypothesis and the essential-image
comparison hypothesis independent, exactly as in the source.
-/

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris
open CategoryTheory.GrothendieckTopology.Derived.Absolute.MayerVietoris

/- Lemma 21.29.2 (0F18): for the ringed-site topology comparison, the bounded-below
essential-image criterion is expressed through the canonical module Mayer--Vietoris condition. -/
@[stacks 0F18]
#check @RingedSite.TopologyComparison.ModuleDerived.MayerVietoris.essImage_iff_condition

/- The representation-independent additive criterion is the generic companion. -/
#check @essImage_iff_condition

/- The additive family corollary keeps the pushout and monomorphism hypotheses explicit. -/
#check @CategoryTheory.GrothendieckTopology.Derived.Absolute.MayerVietoris.essImage_iff_condition_of_mayerVietoris_family

#check @RingedSite.Hom.ModuleDerived.MayerVietoris.Condition

#check @Square
#check @Square.ofCommSq
#check @Square.Condition
#check @CategoryTheory.GrothendieckTopology.Derived.Absolute.rightDerived

end
