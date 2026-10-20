module

public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps between simple intermediate-field extensions

This leaf owns the canonical map from `M⟮x⟯` to `L⟮x⟯` in a tower of fields.
It is independent of any geometric property of the associated spectrum map.
-/

@[expose] public section

open IntermediateField

universe u

namespace IntermediateField.Adjoin.Simple

variable {M L K : Type u}
variable [Field M] [Field L] [Field K]
variable [Algebra M L] [Algebra L K] [Algebra M K] [IsScalarTower M L K]

/-- The canonical containment of `M⟮x⟯` in `L⟮x⟯` after restricting scalars to `M`. -/
@[stacks 0G32 "simple-adjoin containment"]
theorem le (x : K) : M⟮x⟯ ≤ (L⟮x⟯).restrictScalars M := sorry

/-- The canonical non-instance algebra structure on the simple-adjoin extension. -/
@[stacks 0G32 "simple-adjoin algebra owner"]
noncomputable abbrev algebra (x : K) : Algebra M⟮x⟯ L⟮x⟯ :=
  (IntermediateField.inclusion (le (M := M) (L := L) x)).toAlgebra

/-- The canonical ring map from `M⟮x⟯` to `L⟮x⟯`. -/
@[stacks 0G32 "simple-adjoin map"]
noncomputable abbrev map (x : K) : M⟮x⟯ →+* L⟮x⟯ :=
  @algebraMap M⟮x⟯ L⟮x⟯ _ _ (algebra (M := M) (L := L) (K := K) x)

end IntermediateField.Adjoin.Simple
