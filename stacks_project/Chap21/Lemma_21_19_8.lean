/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion.Derived
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.19.8

Torsion for abelian sheaves is a local finite-order condition.  The derived comparison is the
specialization of the generic weak-Serre comparison to this reusable object property.
-/

/- Lemma 21.19.8 (0DD7): the derived category of torsion abelian sheaves is equivalent to the
full subcategory of the ambient derived category whose cohomology sheaves are torsion. -/
@[stacks 0DD7]
#check @CategoryTheory.Sheaf.Torsion.DerivedComparison.isEquivalence

#check @CategoryTheory.Sheaf.IsLocallyTorsion
#check @CategoryTheory.Sheaf.torsion
#check @CategoryTheory.Sheaf.Torsion.isSerre
#check @CategoryTheory.DerivedCategory.CohomologyIn.Comparison.functor
