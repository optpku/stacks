/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Maps.Proper.UniversallyClosed
public import Mathlib.Topology.SeparatedMap
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasi-Proper and Proper Maps

Mathlib owns Bourbaki proper maps as `IsProperMap`.  This leaf adds the
compact-preimage formulation and the pullback-projection bridge used in the
Stacks Project.
-/

@[expose] public section

open Set

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y}

/-- Definition 5.17.2 (3): a map is quasi-proper when it is continuous and
pulls compact subsets back to compact subsets. -/
@[stacks 005O "quasi-proper maps preserve compactness under inverse image"]
structure IsQuasiProperMap (f : X → Y) : Prop where
  /-- A quasi-proper map is continuous. -/
  continuous : Continuous f
  /-- Preimages of compact subsets are compact. -/
  isCompact_preimage : ∀ {K : Set Y}, IsCompact K → IsCompact (f ⁻¹' K)

/-- The defining conditions of a quasi-proper map. -/
@[stacks 005O]
theorem isQuasiProperMap_iff :
    IsQuasiProperMap f ↔
      Continuous f ∧ ∀ {K : Set Y}, IsCompact K → IsCompact (f ⁻¹' K) := sorry

namespace IsProperMap

/-- Definition 5.17.2 (3): every proper map is quasi-proper. -/
@[stacks 005O]
theorem isQuasiProperMap (hf : IsProperMap f) : IsQuasiProperMap f := sorry

/-- Definition 5.17.2 (4): a proper map has a closed second projection after
pullback along a continuous map. -/
@[stacks 005O "proper maps have closed pullback projections"]
theorem isClosedMap_pullback_snd (hf : IsProperMap f)
    {Z : Type*} [TopologicalSpace Z] (g : Z → Y) (hg : Continuous g) :
    IsClosedMap (@Function.Pullback.snd X Y Z f g) := sorry

end IsProperMap

/-- Definition 5.17.2 (3): properness is equivalent to quasi-properness plus
closedness. -/
@[stacks 005O]
theorem isProperMap_iff_isQuasiProperMap_and_isClosedMap :
    IsProperMap f ↔ IsQuasiProperMap f ∧ IsClosedMap f := sorry

/-- Definition 5.17.2 (4): the source pullback formulation of universal
closedness is equivalent to Mathlib's `IsProperMap`. -/
@[stacks 005O "universally closed maps have closed pullback projections"]
theorem isProperMap_iff_isClosedMap_pullback_snd :
    IsProperMap f ↔
      Continuous f ∧
        ∀ (Z : Type (max u v)) [TopologicalSpace Z] (g : Z → Y), Continuous g →
          IsClosedMap (@Function.Pullback.snd X Y Z f g) := sorry
