/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Homeomorph.Lemmas
import StacksCheckRecall

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y} [CompactSpace X] [T2Space Y]

/- Lemma 5.17.8: a continuous bijection from a compact space to a Hausdorff
space is a homeomorphism. -/
@[stacks 08YE]
#check fun (hf : Continuous f) (hbij : Function.Bijective f) ↦
  (isHomeomorph_iff_continuous_bijective.mpr ⟨hf, hbij⟩)
