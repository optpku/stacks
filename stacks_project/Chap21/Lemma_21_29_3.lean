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
# Lemma 21.29.3

The topology-comparison theorem is owned by
`CategoryTheory.GrothendieckTopology.Derived.Absolute.MayerVietoris`; canonical derived-section
maps and their cochain realizations are owned by the derived-sections Mayer--Vietoris leaf.
-/

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris
open CategoryTheory.GrothendieckTopology.Derived.Absolute.MayerVietoris

/- Lemma 21.29.3 (0F19): a `τ`-sheafified-representable pushout with a monomorphic overlap
satisfies the canonical module Mayer--Vietoris condition on every object in the essential image
of the ringed-site topology-comparison right-derived direct image. -/
@[stacks 0F19]
#check @RingedSite.TopologyComparison.ModuleDerived.MayerVietoris.condition_of_essImage

/- The additive theorem is the generic companion below the module specialization. -/
#check @CategoryTheory.GrothendieckTopology.Derived.Absolute.MayerVietoris.condition_of_essImage

#check @CategoryTheory.GrothendieckTopology.Derived.Absolute.pushforward
#check @CategoryTheory.GrothendieckTopology.Derived.Absolute.rightDerived
#check @Square
#check @Square.Condition
#check @Square.Realization
#check @Square.Realization.comparison
#check @Square.Realization.condition_iff_comparison_isIso
#check @Square.Realization.comparison_isIso_of_shortExact

end
