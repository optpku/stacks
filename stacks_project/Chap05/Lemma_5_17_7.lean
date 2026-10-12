/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Maps.Proper.QuasiProper
import StacksCheckRecall

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y} [CompactSpace X] [T2Space Y]

/- Lemma 5.17.7: a continuous map from a compact space to a Hausdorff space
has closed pullback second projections. -/
@[stacks 08YD]
#check fun (hf : Continuous f) (Z : Type (max u v)) [TopologicalSpace Z]
    (g : Z → Y) (hg : Continuous g) ↦
  hf.isProperMap.isClosedMap_pullback_snd g hg
