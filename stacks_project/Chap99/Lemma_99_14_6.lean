/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap99.Lemma_99_14_6_Apex

/-!
# Lemma 99.14.6

The forgetful 1-morphism Polarized ⟶ Spaces'_{fp, flat, proper} is algebraic
in the sense of Definition 97.8.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Lemma 99.14.6: the functor (99.14.1.1) defines a 1-morphism
Polarized ⟶ Spaces'_{fp, flat, proper} of stacks in groupoids over Sch_fppf
which is algebraic in the sense of Definition 97.8.1. -/
@[stacks 0D41]
instance instAlgebraicStack_twoFibreProduct
    (ξ : FpFlatProperGroupoids (⊤_ Scheme.{u})) :
    AlgebraicStack (twoFibreProduct ξ) :=
  sorry

end AlgebraicGeometry.Polarized
