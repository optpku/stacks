/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import stacks_project.Chap10.Lemma_10_75_3_Support

/-!
# Lemma 10.75.3

@stack 00M1
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ ComplexShape

universe u

section


variable {R : Type u} [Ring R]

/-- The degree-`n` component of the canonical map from the total complex of `A` to its
column-cokernel complex, obtained by flipping `A` and using the row comparison. -/
noncomputable def totalToColumnCokernelComponent
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) (n : ℕ) :
    (A.total (down ℕ)).X n ⟶ columnCokernelObject A n :=
  (A.totalFlipIso (down ℕ)).inv.f n ≫ totalToRowCokernelComponent A.flip n

/-- The components of `totalToColumnCokernel` commute with the differentials. -/
theorem totalToColumnCokernel_comm
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (n n' : ℕ) (_hnn' : (down ℕ).Rel n n') :
    totalToColumnCokernelComponent A n ≫ (columnCokernelComplex A).d n n' =
      (A.total (down ℕ)).d n n' ≫ totalToColumnCokernelComponent A n' := sorry

/-- The canonical chain map from the total complex of `A` to its column-cokernel complex. -/
noncomputable def totalToColumnCokernel
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) :
    A.total (down ℕ) ⟶ columnCokernelComplex A where
  f := totalToColumnCokernelComponent A
  comm' := totalToColumnCokernel_comm A

/-- The column comparison is the row comparison for the flipped bicomplex, precomposed with
total-complex symmetry. -/
theorem totalToColumnCokernel_eq_flip
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)) :
    totalToColumnCokernel A =
      (A.totalFlipIso (down ℕ)).inv ≫ totalToRowCokernel A.flip := sorry

/-- If the columns of `A` resolve its column-cokernel complex, the canonical total-complex
comparison is a quasi-isomorphism. -/
theorem totalToColumnCokernel_quasiIso
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hcols : ColumnsResolve A) :
    QuasiIso (totalToColumnCokernel A) := sorry

/-- Lemma 10.75.3 (1): if every row of `A` resolves the corresponding term of
`rowCokernelComplex A` and every column resolves the corresponding term of
`columnCokernelComplex A`, their homology groups are canonically isomorphic. -/
@[stacks 00M1 "(1)"]
noncomputable def resolved_double_complex_homology_comparison
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) (hcols : ColumnsResolve A) (i : ℕ) :
    (rowCokernelComplex A).homology i ≅ (columnCokernelComplex A).homology i :=
  letI : QuasiIso (totalToRowCokernel A) := totalToRowCokernel_quasiIso A hrows
  letI : QuasiIso (totalToColumnCokernel A) := totalToColumnCokernel_quasiIso A hcols
  (isoOfQuasiIsoAt (totalToRowCokernel A) i).symm ≪≫
    isoOfQuasiIsoAt (totalToColumnCokernel A) i

/-- Lemma 10.75.3 (2): the canonical homology comparison is functorial in morphisms of double
complexes whose rows and columns satisfy the resolution hypotheses. -/
@[stacks 00M1 "(2)"]
theorem resolved_double_complex_homology_comparison_naturality
    {A B : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ)}
    (hrowsA : RowsResolve A) (hcolsA : ColumnsResolve A)
    (hrowsB : RowsResolve B) (hcolsB : ColumnsResolve B)
    (f : A ⟶ B) (i : ℕ) :
    homologyMap (rowCokernelMap f) i ≫
        (resolved_double_complex_homology_comparison B hrowsB hcolsB i).hom =
      (resolved_double_complex_homology_comparison A hrowsA hcolsA i).hom ≫
        homologyMap (columnCokernelMap f) i := sorry

end


#check @totalToColumnCokernelComponent
#check @totalToColumnCokernel_comm
#check @totalToColumnCokernel
#check @totalToColumnCokernel_eq_flip
#check @totalToColumnCokernel_quasiIso
#check @resolved_double_complex_homology_comparison
#check @resolved_double_complex_homology_comparison_naturality

#print axioms totalToColumnCokernelComponent
#print axioms totalToColumnCokernel
#print axioms resolved_double_complex_homology_comparison
