/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Krull Dimension under Maps

Dimension comparison along surjective maps that lift either direction of the
specialization relation.
-/

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [QuasiSober Y] [T0Space Y] {f : X → Y}

namespace Continuous

/-- A continuous surjective map lifting specializations does not increase topological Krull
dimension of a quasi-sober `T₀` target. -/
@[stacks 02JF]
theorem topologicalKrullDim_le_of_surjective_of_specializingMap
    (hf : Continuous f) (hsurj : Function.Surjective f) (hlift : SpecializingMap f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := sorry

/-- A continuous surjective map lifting generalizations does not increase topological Krull
dimension of a quasi-sober `T₀` target. -/
@[stacks 02JF]
theorem topologicalKrullDim_le_of_surjective_of_generalizingMap
    (hf : Continuous f) (hsurj : Function.Surjective f) (hlift : GeneralizingMap f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := sorry

/-- A continuous surjective map lifting either specializations or generalizations does not
increase topological Krull dimension. -/
@[stacks 02JF]
theorem topologicalKrullDim_le_of_surjective_of_specializing_or_generalizingMap
    (hf : Continuous f) (hsurj : Function.Surjective f)
    (hlift : SpecializingMap f ∨ GeneralizingMap f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := sorry

end Continuous
