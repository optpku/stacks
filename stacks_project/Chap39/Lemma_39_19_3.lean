/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Saturation
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 39.19.3: if the source and target maps of a groupoid scheme are quasi-compact and flat
and its object scheme is quasi-separated, the saturation of a quasi-compact open is the
intersection of a nonempty family of quasi-compact opens. -/
@[stacks 0APA] #check
  (AlgebraicGeometry.GroupoidScheme.exists_compactOpens_image_preimage :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      [QuasiCompact G.s.left] [Flat G.s.left] [QuasiCompact G.t.left] [Flat G.t.left]
      [QuasiSeparatedSpace G.U.left] (W : CompactOpens G.U.left),
      ∃ 𝒱 : Set (CompactOpens G.U.left), 𝒱.Nonempty ∧
        G.t.left '' (G.s.left ⁻¹' (W : Set G.U.left)) =
          ⋂ V ∈ 𝒱, (V : Set G.U.left))

end AlgebraicGeometry.GroupoidScheme
