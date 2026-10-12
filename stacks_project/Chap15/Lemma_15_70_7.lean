/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude.Local
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.70.7

@stack 0AVJ
-/

/-!
# Lemma 15.70.7: the local residue-field criterion

The reusable theorem is a specialization of the Noetherian ideal-quotient criterion.  The
bounded-below object, finite cohomology hypothesis, and canonical residue field all remain visible
on its public surface.
-/

/- Lemma 15.70.7, tag `0AVJ`: over a local Noetherian ring, finite injective dimension is
equivalent to eventual vanishing of derived Ext from the residue field. -/
@[stacks 0AVJ "Lemma 15.70.7"]
#check @CategoryTheory.DerivedCategory.HasFiniteInjectiveDimension.iff_eventually_residueField_ext

/- The underlying Noetherian criterion remains directly importable for nonlocal applications. -/
#check @CategoryTheory.DerivedCategory.HasFiniteInjectiveDimension.iff_eventually_idealQuotient_ext
