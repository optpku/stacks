/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry.Scheme

/- Lemma 26.21.6: quasi-separatedness is controlled by compact intersections of affine opens
over a common affine target. -/
@[stacks 01KO] #check
  Hom.quasiSeparated_iff_affineInter_isCompact

@[stacks 01KO] #check
  Hom.quasiSeparated_iff_affineInter_finiteCover

@[stacks 01KO] #check
  Hom.quasiSeparated_iff_exists_affineCover_hasCompactIntersections

#check Hom.quasiSeparated_iff_pullback_quasiSeparatedSpace
#check Hom.quasiSeparated_iff_exists_affineCover_pullback
#check isCompact_iff_finite_and_eq_biUnion_affineOpens
#check AffineOpenCover.HasCompactIntersections
#check AffineOpenCover.quasiSeparatedSpace_iff_hasCompactIntersections
#check AffineOpenCover.hasCompactIntersections_iff_finiteCover

end AlgebraicGeometry.Scheme
