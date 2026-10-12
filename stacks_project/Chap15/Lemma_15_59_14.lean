/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
import StacksCheckRecall

@[expose] public section

/-!
# Symmetry of the derived tensor product

@stack 0BYI
-/

open CategoryTheory

/- Lemma 15.59.14, tag `0BYI`: the two-variable derived tensor product is symmetric.  The
generic owner applies to `ModuleCat R` through its canonical derived-tensor instance. -/
@[stacks 0BYI "derived tensor symmetry"]
#check @DerivedCategory.DerivedTensor.Bifunctor.comm

/- The symmetry is functorial in both derived-complex variables. -/
@[stacks 0BYI "naturality of derived tensor symmetry"]
#check @DerivedCategory.DerivedTensor.Bifunctor.comm_hom_naturality

/- The comparison is induced by the signed Koszul braiding on complex representatives. -/
@[stacks 0BYI "Koszul sign compatibility"]
#check @DerivedCategory.DerivedTensor.Bifunctor.braiding_hom_counit
