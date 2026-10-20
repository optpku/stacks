module

public import Mathlib.Algebra.Homology.QuasiIso
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Support
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison

/-!
# Quasi-Isomorphism Criteria for Double-Complex Comparisons

The canonical axis-to-total maps are defined in `DoubleComplex/TotalComparison`.  This higher
leaf adds support and transverse-exactness hypotheses only where quasi-isomorphism conclusions
need them.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape HomologicalComplex

noncomputable section

universe u v

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Total.Map

/-- A columnwise quasi-isomorphism between double complexes with finite antidiagonal support
induces a quasi-isomorphism on total complexes. -/
theorem quasiIso_of_columnwise
    {A B : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]
    (hA : AntidiagonalSupport.Finite A) (hB : AntidiagonalSupport.Finite B)
    (f : A ⟶ B) (hf : ∀ p : ℤ, QuasiIso (f.f p)) :
    QuasiIso (HomologicalComplex₂.total.map f (up ℤ)) := sorry

/-- A rowwise quasi-isomorphism between double complexes with finite antidiagonal support induces
a quasi-isomorphism on total complexes. -/
theorem quasiIso_of_rowwise
    {A B : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]
    (hA : AntidiagonalSupport.Finite A) (hB : AntidiagonalSupport.Finite B)
    (f : A ⟶ B)
    (hf : ∀ q : ℤ,
      QuasiIso (((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map f).f q)) :
    QuasiIso (HomologicalComplex₂.total.map f (up ℤ)) := sorry

end Total.Map

namespace ZeroRow

namespace ToTotal

/-- If transverse homology is concentrated on the zeroth row and the prescribed row map
identifies degree-zero vertical homology, then the row-to-total map is a quasi-isomorphism. -/
theorem quasiIso_of_exact
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (hfin : AntidiagonalSupport.Finite A)
    (hexact : ∀ p q : ℤ, q ≠ 0 → (A.X p).ExactAt q)
    (f : K ⟶ A.zeroRow) (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0)
    (hfHomology : ∀ p : ℤ, IsIso (ZeroRow.Homology.map f hf p)) :
    QuasiIso (ZeroRow.ToTotal.map f hf) := sorry

/-- Lemma 12.25.4: vanishing below the zeroth row and exactness above it reduce the transverse
homology condition to the cycle-map condition. -/
@[stacks 0133 "quasi-isomorphism from the zeroth row to the total complex"]
theorem quasiIso_of_vanish_below
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (hfin : AntidiagonalSupport.Finite A)
    (hvanish : ∀ p q : ℤ, q < 0 → IsZero ((A.X p).X q))
    (hexact : ∀ p q : ℤ, 0 < q → (A.X p).ExactAt q)
    (f : K ⟶ A.zeroRow) (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0)
    (hfCycles : ∀ p : ℤ, IsIso (ZeroRow.Cycles.map f hf p)) :
    QuasiIso (ZeroRow.ToTotal.map f hf) := sorry

end ToTotal

end ZeroRow

namespace ZeroColumn

namespace ToTotal

/-- If transverse homology is concentrated on the zeroth column and the prescribed column map
identifies degree-zero horizontal homology, then the column-to-total map is a quasi-isomorphism. -/
theorem quasiIso_of_exact
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (hfin : AntidiagonalSupport.Finite A)
    (hexact : ∀ q p : ℤ, p ≠ 0 → (A.flip.X q).ExactAt p)
    (f : K ⟶ A.zeroColumn) (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0)
    (hfHomology : ∀ q : ℤ, IsIso (ZeroColumn.Homology.map f hf q)) :
    QuasiIso (ZeroColumn.ToTotal.map f hf) := sorry

/-- Lemma 12.25.4 in the exchanged orientation: vanishing left of the zeroth column and
exactness to its right reduce the transverse homology condition to the cycle-map condition. -/
@[stacks 0133 "quasi-isomorphism from the zeroth column to the total complex"]
theorem quasiIso_of_vanish_left
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (hfin : AntidiagonalSupport.Finite A)
    (hvanish : ∀ p q : ℤ, p < 0 → IsZero ((A.X p).X q))
    (hexact : ∀ q p : ℤ, 0 < p → (A.flip.X q).ExactAt p)
    (f : K ⟶ A.zeroColumn) (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0)
    (hfCycles : ∀ q : ℤ, IsIso (ZeroColumn.Cycles.map f hf q)) :
    QuasiIso (ZeroColumn.ToTotal.map f hf) := sorry

end ToTotal

end ZeroColumn

end HomologicalComplex₂
