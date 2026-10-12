/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.DifferentialRescale
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Initial Pages Associated to a Double Complex

This file owns the two canonical page-zero presentations and the cochain complexes obtained after
taking homology in either direction.  The second page-one complex is the signed rescaling of the
first construction applied to the flipped double complex.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The first page-zero entry of a cohomological double complex. -/
@[stacks 0130 "the first page-zero entries"]
abbrev First.PageZero.entry (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) : C :=
  (K.X p).X q

/-- The signed vertical differential on the first page-zero presentation. -/
@[stacks 0130 "the first page-zero differential"]
abbrev First.PageZero.differential (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) :
    First.PageZero.entry K p q ⟶ First.PageZero.entry K p (q + 1) :=
  p.negOnePow • (K.X p).d q (q + 1)

/-- The second page-zero entry, obtained by flipping the two directions. -/
@[stacks 0130 "the second page-zero entries"]
abbrev Second.PageZero.entry (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) : C :=
  (K.flip.X p).X q

/-- The second page-zero presentation is the transposed entry of the original double complex. -/
@[simp]
theorem Second.PageZero.entry_eq (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) :
    Second.PageZero.entry K p q = (K.X q).X p := sorry

/-- The horizontal differential on the second page-zero presentation. -/
@[stacks 0130 "the second page-zero differential"]
abbrev Second.PageZero.differential
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) :
    Second.PageZero.entry K p q ⟶ Second.PageZero.entry K p (q + 1) :=
  (K.flip.X p).d q (q + 1)

/-- The second page-zero differential is the first differential of the original double complex. -/
@[simp]
theorem Second.PageZero.differential_eq
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) :
    Second.PageZero.differential K p q = (K.d q (q + 1)).f p := sorry

section Homology

variable [CategoryWithHomology C]

/-- The first page-one cochain complex, obtained by taking vertical homology in degree `q`. -/
@[stacks 0130 "the first page-one complex"]
abbrev First.PageOne.complex (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (q : ℤ) :
    CochainComplex C ℤ :=
  ((HomologicalComplex.homologyFunctor C (up ℤ) q).mapHomologicalComplex (up ℤ)).obj K

/-- A first page-one entry is the vertical homology of the corresponding column. -/
@[simp]
theorem First.PageOne.complex_X
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) :
    (First.PageOne.complex K q).X p = (K.X p).homology q := sorry

/-- The first page-one differential is induced by the horizontal differential. -/
@[simp]
theorem First.PageOne.complex_d
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) :
    (First.PageOne.complex K q).d p (p + 1) = homologyMap (K.d p (p + 1)) q := sorry

/-- The second page-one cochain complex, obtained from the flipped first page and the standard
sign rescaling in vertical degree `q`. -/
@[stacks 0130 "the second page-one complex"]
abbrev Second.PageOne.complex (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (q : ℤ) :
    CochainComplex C ℤ :=
  (First.PageOne.complex K.flip q).rescaleDifferential (q.negOnePow : ℤ)

/-- A second page-one entry is the horizontal homology of the corresponding row. -/
@[simp]
theorem Second.PageOne.complex_X
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) :
    (Second.PageOne.complex K q).X p = (K.flip.X p).homology q := sorry

/-- The second page-one differential is the signed homology map in the other direction. -/
@[simp]
theorem Second.PageOne.complex_d
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) :
    (Second.PageOne.complex K q).d p (p + 1) =
      q.negOnePow • homologyMap (K.flip.d p (p + 1)) q := sorry

/-- The first page-one entry at bidegree `(p,q)`. -/
@[stacks 0130 "the first page-one entries"]
abbrev First.PageOne.entry (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) : C :=
  (First.PageOne.complex K q).X p

/-- The first page-one differential at bidegree `(p,q)`. -/
@[stacks 0130 "the first page-one differential"]
abbrev First.PageOne.differential
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) :
    First.PageOne.entry K p q ⟶ First.PageOne.entry K (p + 1) q :=
  (First.PageOne.complex K q).d p (p + 1)

/-- The second page-one entry at bidegree `(p,q)`. -/
@[stacks 0130 "the second page-one entries"]
abbrev Second.PageOne.entry (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) : C :=
  (Second.PageOne.complex K q).X p

/-- The second page-one differential at bidegree `(p,q)`. -/
@[stacks 0130 "the second page-one differential"]
abbrev Second.PageOne.differential
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) :
    Second.PageOne.entry K p q ⟶ Second.PageOne.entry K (p + 1) q :=
  (Second.PageOne.complex K q).d p (p + 1)

/-- The first page-two entry, obtained by taking horizontal homology of the first page-one
complex. -/
@[stacks 0130 "the first page-two entries"]
abbrev First.PageTwo.entry (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) : C :=
  (First.PageOne.complex K q).homology p

/-- The second page-two entry, obtained by taking vertical homology of the second page-one
complex. -/
@[stacks 0130 "the second page-two entries"]
abbrev Second.PageTwo.entry (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) : C :=
  (Second.PageOne.complex K q).homology p

end Homology

end HomologicalComplex₂
