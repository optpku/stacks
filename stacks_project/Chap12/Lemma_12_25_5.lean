/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalHomotopy
import StacksCheckRecall

/-!
# Lemma 12.25.5

Source-facing checks for the comparison between a complex and the total complex of a
cochain-complex-valued cochain complex.  The reusable maps and homotopies are owned by
`HomologicalComplex₂` in `ReasLib`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
variable [A.HasTotal (up ℤ)]
variable (a : (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M ⟶ A)
variable (ha : HomologicalComplex.homotopyEquivalences (CochainComplex C ℤ) (up ℤ) a)

/- The totalization owner constructs the homotopy on total complexes directly from an outer
homotopy, without requiring coproducts for unrelated bicomplexes. -/
#check HomologicalComplex₂.Total.Homotopy.First.of

/- Explicit homotopy equivalences of bicomplexes induce explicit homotopy equivalences of their
total complexes. -/
#check HomologicalComplex₂.Total.Homotopy.First.equiv

/- The map `M^• ⟶ A^{0,•}` extracted from `M^•[0] ⟶ A^{•,•}`. -/
#check (HomologicalComplex₂.ZeroColumn.Single.toColumn a : M ⟶ A.X 0)

/- The induced comparison `M^• ⟶ Tot(A^{•,•})`. -/
#check (HomologicalComplex₂.ZeroColumn.Single.toTotal a : M ⟶ A.total (up ℤ))

/- Lemma 12.25.5 [0FKH]: a homotopy equivalence `M^•[0] ⟶ A^{•,•}` induces a homotopy
equivalence `M^• ⟶ Tot(A^{•,•})`. -/
@[stacks 0FKH]
#check (HomologicalComplex₂.ZeroColumn.Single.toTotal_isHomotopyEquivalence ha :
  HomologicalComplex.homotopyEquivalences C (up ℤ)
    (HomologicalComplex₂.ZeroColumn.Single.toTotal a))
