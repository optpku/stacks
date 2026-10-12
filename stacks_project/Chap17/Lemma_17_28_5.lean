/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials.OpenSubset
import StacksCheckRecall

@[expose] public section

/- Lemma 17.28.5 (08RQ): restriction to an open subset commutes canonically with relative
differentials and preserves the universal derivation. -/
@[stacks 08RQ]
#check @TopCat.Sheaf.RelativeDifferentials.OpenSubset.iso
#check @TopCat.Sheaf.RelativeDifferentials.OpenSubset.iso_hom

#check @TopCat.Sheaf.RelativeDifferentials.OpenSubset.comparison_spec
#check @TopCat.Sheaf.RelativeDifferentials.OpenSubset.eq_comparison
