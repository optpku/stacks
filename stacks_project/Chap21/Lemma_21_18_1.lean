/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.KFlat
import StacksCheckRecall

@[expose] public section

/-!
# Pullback of K-flat complexes

The reusable owner is stated for a bundled morphism of commutative ringed sites.  This is the
site-presented specialization currently supported by ReasLib; the source's fully presentation-
independent statement for arbitrary morphisms of ringed topoi requires a future ringed-topos
module-pullback layer.
-/

/- Lemma 21.18.1 (0G7E), site-presented commutative form: module pullback sends a K-flat,
termwise-flat cochain complex to one with both properties. -/
@[stacks 0G7E]
#check @RingedSite.Hom.modulePullbackComplex.isKFlat_and_isTermwiseFlat

#check @RingedSite.Hom.modulePullbackComplex
#check @RingedSite.Hom.modulePullbackComplex.obj_X
#check @RingedSite.Hom.modulePullbackComplex.isTermwiseFlat
#check @RingedSite.Hom.modulePullbackComplex.isKFlat_of_isTermwiseFlat
