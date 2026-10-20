module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived comparison for good lower truncations

When the source complex is cohomologically supported in degrees `≥ a`, the canonical projection to
its good lower truncation is a quasi-isomorphism.  This leaf packages the resulting derived
comparison as both an `IsIso` fact and an explicit `Iso` for downstream model transport.
@stack 0E1U
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.DerivedCategory.Q

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasDerivedCategory.{w} C]

/-- Stacks `0E1U`: the derived image of a good-lower-truncation projection is an isomorphism above
the cutoff. -/
@[stacks 0E1U "derived good-lower-truncation comparison"]
theorem isIso_map_πTruncGE
    (K : CochainComplex C ℤ) (a : ℤ) (hK : K.IsGE a) :
    IsIso (DerivedCategory.Q.map (K.πTruncGE a)) := sorry

/-- Stacks `0E1U`: the canonical derived isomorphism from a complex to its good lower truncation. -/
@[stacks 0E1U "derived good-lower-truncation isomorphism"]
noncomputable def truncGEIso
    (K : CochainComplex C ℤ) (a : ℤ) (hK : K.IsGE a) :
    DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj (K.truncGE a) :=
  @asIso _ _ _ _ (DerivedCategory.Q.map (K.πTruncGE a))
    (isIso_map_πTruncGE K a hK)

/-- Stacks `0E1U`: the forward map of `truncGEIso` is the derived image of the canonical
truncation projection. -/
@[simp, stacks 0E1U "forward map of the derived good-lower-truncation isomorphism"]
theorem truncGEIso_hom
    (K : CochainComplex C ℤ) (a : ℤ) (hK : K.IsGE a) :
    (truncGEIso K a hK).hom = DerivedCategory.Q.map (K.πTruncGE a) := sorry

end CategoryTheory.DerivedCategory.Q

end
