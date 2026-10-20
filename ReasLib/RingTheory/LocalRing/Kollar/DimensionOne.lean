/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.DimensionOne
public import ReasLib.RingTheory.LocalRing.Kollar.Criterion
public import ReasLib.RingTheory.RegularLocalRing.DimensionOne

@[expose] public section

/-!
# Kollar's exceptional extension in dimension one

@stack 00P9

This leaf combines Kollar's local-ring criterion with the dimension-one depth
and cotangent-space bounds.  The conclusion uses the neutral exceptional-
extension owner rather than repeating its existential data.
-/

universe u

namespace IsLocalRing.Kollar

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Lemma 10.119.3 (00P9): a one-dimensional Noetherian local ring of
embedding dimension greater than one has a Kollar exceptional extension. -/
@[stacks 00P9]
theorem hasExceptionalExtension_of_embeddingDimension_gt_one
    (hdim : ringKrullDim R = 1)
    (hcot : 1 < Module.finrank (ResidueField R) (CotangentSpace R)) :
    HasExceptionalExtension R := sorry

end IsLocalRing.Kollar
