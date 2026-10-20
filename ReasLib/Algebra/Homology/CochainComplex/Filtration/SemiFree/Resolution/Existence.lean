module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree.Cover.Existence
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree.Resolution
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Existence of Semi-Free Resolutions

This leaf records the iterative construction of a semi-free resolution from
two-step semi-free covers.  The resolution data owner itself does not depend
on this construction.
-/

noncomputable section

universe u

namespace CochainComplex.SemiFreeResolution

variable {A : Type u} [Ring A]

/-- Lemma 22.20.4 (09KP): every differential graded `A`-module admits a semi-free
resolution. -/
@[stacks 09KP]
theorem nonempty (M : ModuleCat.DGMod A) : Nonempty (SemiFreeResolution M) := sorry

end CochainComplex.SemiFreeResolution
