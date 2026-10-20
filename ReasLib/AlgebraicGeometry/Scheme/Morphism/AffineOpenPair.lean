module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pairs of affine opens over a common affine target
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Explicit data exhibiting two affine opens of `X` inside the inverse image of one affine
open of `S`. -/
@[stacks 01KO "common affine target data"]
structure Scheme.Hom.CommonAffineTarget
    (f : X ⟶ S) (U V : X.affineOpens) where
  /-- The chosen affine open in the target. -/
  target : S.affineOpens
  /-- The first affine open maps into the chosen target open. -/
  left_le : U ≤ f ⁻¹ᵁ target
  /-- The second affine open maps into the chosen target open. -/
  right_le : V ≤ f ⁻¹ᵁ target

/-- Package a chosen affine target and the two containment proofs as common-affine-target
data. -/
def Scheme.Hom.CommonAffineTarget.ofTarget
    {f : X ⟶ S} {U V : X.affineOpens}
    (W : S.affineOpens) (hU : U ≤ f ⁻¹ᵁ W) (hV : V ≤ f ⁻¹ᵁ W) :
    f.CommonAffineTarget U V where
  target := W
  left_le := hU
  right_le := hV

/-- Two affine opens of `X` have a common affine target under `f` when both map into one affine
open of `S`. -/
@[stacks 01KO "existence of a common affine target"]
def Scheme.Hom.HasCommonAffineTarget
    (f : X ⟶ S) (U V : X.affineOpens) : Prop :=
  ∃ W : S.affineOpens, U ≤ f ⁻¹ᵁ W ∧ V ≤ f ⁻¹ᵁ W

/-- Existence of a common affine target is equivalent to inhabitation of the bundled data. -/
@[stacks 01KO "common affine target as bundled data"]
theorem Scheme.Hom.hasCommonAffineTarget_iff_nonempty
    (f : X ⟶ S) (U V : X.affineOpens) :
    f.HasCommonAffineTarget U V ↔ Nonempty (f.CommonAffineTarget U V) := sorry

/-- Having a common affine target is symmetric in the two source opens. -/
@[stacks 01KO "symmetry of common affine targets"]
theorem Scheme.Hom.hasCommonAffineTarget_comm
    (f : X ⟶ S) (U V : X.affineOpens) :
    f.HasCommonAffineTarget U V ↔ f.HasCommonAffineTarget V U := sorry

namespace Scheme.Hom.CommonAffineTarget

variable {f : X ⟶ S} {U V : X.affineOpens}

/-- Exchange the two source opens while retaining the same affine target. -/
@[stacks 01KO "swap common affine target data"]
def swap (W : f.CommonAffineTarget U V) : f.CommonAffineTarget V U where
  target := W.target
  left_le := W.right_le
  right_le := W.left_le

/-- Swapping common-affine-target data twice recovers the original data. -/
@[stacks 01KO "involutivity of common affine target swap"]
theorem swap_swap (W : f.CommonAffineTarget U V) : W.swap.swap = W := sorry

/-- Explicit common-affine-target data supplies the corresponding existence property. -/
@[stacks 01KO "common affine target data gives existence"]
theorem has (W : f.CommonAffineTarget U V) :
    f.HasCommonAffineTarget U V := sorry

end Scheme.Hom.CommonAffineTarget

/-- The common-target existence property can be used in the opposite order. -/
@[stacks 01KO "common affine target symmetry"]
theorem Scheme.Hom.HasCommonAffineTarget.symm
    {f : X ⟶ S} {U V : X.affineOpens}
    (h : f.HasCommonAffineTarget U V) : f.HasCommonAffineTarget V U := sorry

end AlgebraicGeometry
