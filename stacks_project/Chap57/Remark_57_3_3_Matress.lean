/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.Matress

@[expose] public section

open CategoryTheory ComplexShape

universe v

#check (HomologicalComplex₂.Matress :
  ∀ K : HomologicalComplex₂ AddCommGrpCat.{v} (up ℤ) (up ℤ),
    (K ≅ K.bidegreeShift 3 (-3)) → Prop)

#check (HomologicalComplex₂.Matress.periodComponent :
  ∀ {K : HomologicalComplex₂ AddCommGrpCat.{v} (up ℤ) (up ℤ)}
    (period : K ≅ K.bidegreeShift 3 (-3)) (p q p' q' : ℤ),
    p' = p + 3 → q' = q - 3 →
      CategoryTheory.Iso (C := AddCommGrpCat.{v}) ((K.X p).X q) ((K.X p').X q'))

end
