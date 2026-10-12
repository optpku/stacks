/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Monoidal
import StacksCheckRecall

@[expose] public section

/-!
# Remark 21.19.7

The relative derived cup product is the tensorator of the canonical lax monoidal structure on
derived pushforward. Its adjoint-side description is owned by the same ReasLib module.
-/

/- Remark 21.19.7 (0B6C): for a morphism of ringed topoi, the relative derived cup product is
the mate of the derived-pullback tensor comparison followed by the two counits. -/
@[stacks 0B6C]
#check @RingedSite.Hom.modulePushforwardDerived.cupProduct

#check @RingedSite.Hom.modulePushforwardDerived.map_cupProduct_comp_counit
