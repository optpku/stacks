module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed support bounds for chain complexes

This leaf owns the support condition saying that a chain complex vanishes in every
degree strictly above a specified degree, relative to the supplied degree relation.
It is independent of augmentations, resolutions, and module structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

section Definition

-- The additive shape assumptions come from the `ChainComplex` carrier itself; the bound
-- contributes only the displayed strict relation.
variable {ι : Type w} [AddRightCancelSemigroup ι] [One ι] [LT ι]

/-- Tag `0CXD`: a chain complex is bounded above by `d` when every term in degree strictly
greater than `d` is zero. -/
@[stacks 0CXD "upper support bound for chain complexes"]
def IsBoundedLE (F : ChainComplex C ι) (d : ι) : Prop :=
  ∀ n : ι, d < n → IsZero (F.X n)

end Definition

section Monotonicity

variable {ι : Type w} [AddRightCancelSemigroup ι] [One ι] [Preorder ι]

/-- Raising an upper support bound preserves boundedness. -/
@[stacks 0CXD "monotonicity of chain-complex support bounds"]
theorem IsBoundedLE.of_le
    {F : ChainComplex C ι} {d e : ι}
    (hF : IsBoundedLE F d) (hde : d ≤ e) :
    IsBoundedLE F e := sorry

end Monotonicity

end ChainComplex
