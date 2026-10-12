/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# The two parts of the Hom-complex differential

For cochain complexes in any preadditive category, the Hom-complex differential splits into
postcomposition with the target differential and signed precomposition with the source
differential.  This leaf owns those two operations independently of any enrichment or concrete
module category.

@stack 0A8H
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace Cochain

/-- Postcomposition with the target differential raises the degree of a cochain by one. -/
@[stacks 0A8H "postcomposition part of the Hom-complex differential"]
def postDifferential (M N : CochainComplex C ℤ) (n : ℤ)
    (z : Cochain M N n) : Cochain M N (n + 1) :=
  z.comp (Cochain.diff N) rfl

/-- Precomposition with the source differential raises the degree of a cochain by one. -/
@[stacks 0A8H "precomposition part of the Hom-complex differential"]
def preDifferential (M N : CochainComplex C ℤ) (n : ℤ)
    (z : Cochain M N n) : Cochain M N (n + 1) :=
  (Cochain.diff M).comp z (add_comm 1 n)

/-- Postcomposition with the target differential is additive. -/
@[stacks 0A8H "additivity of Hom postcomposition"]
theorem postDifferential_add (M N : CochainComplex C ℤ) (n : ℤ)
    (f g : Cochain M N n) :
    postDifferential M N n (f + g) =
      postDifferential M N n f + postDifferential M N n g := sorry

/-- Precomposition with the source differential is additive. -/
@[stacks 0A8H "additivity of Hom precomposition"]
theorem preDifferential_add (M N : CochainComplex C ℤ) (n : ℤ)
    (f g : Cochain M N n) :
    preDifferential M N n (f + g) =
      preDifferential M N n f + preDifferential M N n g := sorry

end Cochain

/-- The Hom-complex differential is the sum of target postcomposition and signed source
precomposition. -/
@[stacks 0A8H "formula for the Hom-complex differential"]
theorem δ_eq_post_add_pre (M N : CochainComplex C ℤ) (n : ℤ)
    (z : Cochain M N n) :
    δ n (n + 1) z =
      Cochain.postDifferential M N n z +
        (n + 1).negOnePow • Cochain.preDifferential M N n z := sorry

/- The component and degree-zero component formulas below remain owned by Mathlib; this recall
block makes them visible from the ReasLib Hom-complex differential boundary without introducing
an alias theorem. -/

end CochainComplex.HomComplex
