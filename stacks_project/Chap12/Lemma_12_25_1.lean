/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.Pages
import StacksCheckRecall

/-!
# Lemma 12.25.1

Source-facing checks for the initial pages of the two spectral sequences associated to a
cohomological double complex.  The reusable constructions are owned by
`HomologicalComplex₂` in `ReasLib`.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K : HomologicalComplex₂ C (up ℤ) (up ℤ)} (p q : ℤ)

/- Lemma 12.25.1 (1): the first page-zero entry is `K^{p,q}`. -/
@[stacks 0130]
#check (HomologicalComplex₂.First.PageZero.entry K p q : C)

/- Lemma 12.25.1 (2): its differential is the signed vertical differential. -/
@[stacks 0130]
#check (HomologicalComplex₂.First.PageZero.differential K p q :
  HomologicalComplex₂.First.PageZero.entry K p q ⟶
    HomologicalComplex₂.First.PageZero.entry K p (q + 1))

/- Lemma 12.25.1 (3): the second page-zero entry is the transposed entry `K^{q,p}`. -/
@[stacks 0130]
#check (HomologicalComplex₂.Second.PageZero.entry K p q : C)

/- Lemma 12.25.1 (4): its differential is the horizontal differential of `K`. -/
@[stacks 0130]
#check (HomologicalComplex₂.Second.PageZero.differential K p q :
  HomologicalComplex₂.Second.PageZero.entry K p q ⟶
    HomologicalComplex₂.Second.PageZero.entry K p (q + 1))

section Homology

variable [CategoryWithHomology C]

/- Lemma 12.25.1 (5): the first page-one entries are vertical homology. -/
@[stacks 0130]
#check (HomologicalComplex₂.First.PageOne.entry K p q : C)

/- Lemma 12.25.1 (6): the first page-one differential is induced horizontally. -/
@[stacks 0130]
#check (HomologicalComplex₂.First.PageOne.differential K p q :
  HomologicalComplex₂.First.PageOne.entry K p q ⟶
    HomologicalComplex₂.First.PageOne.entry K (p + 1) q)

/- Lemma 12.25.1 (7): the second page-one entries are horizontal homology. -/
@[stacks 0130]
#check (HomologicalComplex₂.Second.PageOne.entry K p q : C)

/- Lemma 12.25.1 (8): the second page-one differential carries the standard sign. -/
@[stacks 0130]
#check (HomologicalComplex₂.Second.PageOne.differential K p q :
  HomologicalComplex₂.Second.PageOne.entry K p q ⟶
    HomologicalComplex₂.Second.PageOne.entry K (p + 1) q)

/- Lemma 12.25.1 (9): the first page-two entries are the homology of the first page-one
complex. -/
@[stacks 0130]
#check (HomologicalComplex₂.First.PageTwo.entry K p q : C)

/- Lemma 12.25.1 (10): the second page-two entries are the homology of the second page-one
complex. -/
@[stacks 0130]
#check (HomologicalComplex₂.Second.PageTwo.entry K p q : C)

end Homology

end CategoryTheory
