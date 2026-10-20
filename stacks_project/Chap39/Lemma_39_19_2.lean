/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Saturation

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 39.19.2 (1): the target image of the source preimage of any subset is
set-theoretically invariant under a groupoid scheme. -/
@[stacks 03LO] #check
  (AlgebraicGeometry.GroupoidScheme.isSetInvariant_image_preimage :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S) (W : Set G.U.left),
      G.toPreRelation.IsSetInvariant (G.t.left '' (G.s.left ⁻¹' W)))

/- Lemma 39.19.2 (2): when the target map is open, the target image of the
source preimage of an open is an invariant open. -/
@[stacks 03LO] #check
  (AlgebraicGeometry.GroupoidScheme.isOpenInvariant_image_preimage :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      (h_t : IsOpenMap (G.t.left).base) (W : Opens G.U.left),
      G.toPreRelation.IsOpenInvariant (h_t.functor.obj (G.s.left ⁻¹ᵁ W)))

/- Lemma 39.19.2 (3): when the target map is open and both source and target are
quasi-compact, the object scheme has a cover by invariant compact opens. -/
@[stacks 03LO] #check
  (AlgebraicGeometry.GroupoidScheme.exists_invariantCompactOpenCover :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      [QuasiCompact G.s.left] [QuasiCompact G.t.left]
      (h_t : IsOpenMap (G.t.left).base),
      ∃ (ι : Type u) (𝒰 : ι → CompactOpens G.U.left),
        IsOpenCover (fun i ↦ (𝒰 i).toOpens) ∧
          ∀ i, G.toPreRelation.IsOpenInvariant (𝒰 i).toOpens)

end AlgebraicGeometry.GroupoidScheme
