/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
import StacksCheckRecall

@[expose] public section

/-!
# The symmetric derived tensor product

The reusable construction lives in the K-flat localization API.  This file records only its
specialization to modules on a ringed space. The three localization facts remain explicit while
their statement-stage proofs contain placeholders, so they cannot contaminate concrete tensor
data through typeclass search.
-/

/- The reusable proof boundaries for the K-flat localization construction. -/
#check @CategoryTheory.HomotopyCategory.Koszul.homotopyEquivalencesIsMonoidal
#check @CategoryTheory.HomotopyCategory.KFlat.quasiIsoIsMonoidal
#check @CategoryTheory.DerivedCategory.KFlat.localizationIsLocalization

/- Lemma 20.50.6: the derived category `D(𝒪_X)` is a symmetric monoidal category. -/
@[stacks 0FPB]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.symmetricCategory
