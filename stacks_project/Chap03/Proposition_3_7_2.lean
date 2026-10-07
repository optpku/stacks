module

public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

@[expose] public section

noncomputable section

universe u

open Cardinal
open scoped Cardinal

namespace Ordinal

/-- Proposition 3.7.2: for every cardinal `κ` there exists an ordinal whose cofinality is
strictly larger than `κ`. -/
@[stacks 05N3]
theorem exists_cof_gt (κ : Cardinal.{u}) : ∃ o : Ordinal.{u}, κ < o.cof := sorry

end Ordinal
