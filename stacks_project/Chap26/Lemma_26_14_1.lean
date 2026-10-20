/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Gluing

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.LocallyRingedSpace

/- Lemma 26.14.1: locally ringed-space gluing is owned by `GlueData`; its chart maps are open
immersions, jointly cover the glued space, and realize the prescribed overlaps as pullbacks. -/
#check GlueData
@[stacks 01JB] #check CategoryTheory.GlueData.glued
@[stacks 01JB] #check GlueData.ι_isOpenImmersion
@[stacks 01JB] #check GlueData.ι_jointly_surjective
@[stacks 01JB] #check GlueData.vPullbackConeIsLimit

/- The two mapping properties are the outgoing descent theorem and the incoming descent theorem
for arbitrary source opens. The canonical chart-preimage construction is kept separate from that
source-cover API; it is injective, while `existsUnique_hom` gives the descent statement. -/
@[stacks 01JB] #check GlueData.homEquiv
#check CategoryTheory.GlueData.existsUnique_desc
#check CategoryTheory.GlueData.descFamily
#check CategoryTheory.GlueData.ι_descFamily
#check CategoryTheory.GlueData.descFamily_unique
#check CategoryTheory.GlueData.hom_ext
#check GlueData.IncomingDescent
#check GlueData.IncomingDescent.IsInducedBy
#check GlueData.IncomingDescent.overlap_fst
#check GlueData.IncomingDescent.overlap_snd
#check Hom.restrictToOpenImmersion
#check GlueData.chartPreimageMap
#check GlueData.chartPreimageMap_ι
#check GlueData.existsUnique_chartPreimageMap
#check GlueData.chartPreimageOverlap
#check GlueData.chartPreimageOverlap_fst
#check GlueData.chartPreimageOverlap_snd
#check GlueData.chartPreimageOverlap_unique
#check GlueData.chartPreimageOverlap_isPullback
#check GlueData.incomingDescent
#check GlueData.incomingDescent_injective
#check GlueData.IncomingDescent.canonical_isInducedBy
#check GlueData.IncomingDescent.exists_hom
@[stacks 01JB] #check GlueData.IncomingDescent.existsUnique_hom

end AlgebraicGeometry.LocallyRingedSpace
