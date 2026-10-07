module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison.QuasiIso
import StacksCheckRecall

/-!
# Lemma 12.25.4

Source-facing checks for the canonical comparisons from the zeroth row or zeroth column of a
cohomological double complex to its total complex.  The reusable constructions and the symmetric
quasi-isomorphism criteria are owned by `HomologicalComplex₂` in `ReasLib`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex

universe v u

section TotalMap

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B : HomologicalComplex₂ C (up ℤ) (up ℤ)}
variable [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]
variable (hA : HomologicalComplex₂.AntidiagonalSupport.Finite A)
variable (hB : HomologicalComplex₂.AntidiagonalSupport.Finite B)
variable (g : A ⟶ B)
variable (hgColumn : ∀ p : ℤ, QuasiIso (g.f p))
variable (hgRow : ∀ q : ℤ,
  QuasiIso (((HomologicalComplex₂.flipFunctor C (up ℤ) (up ℤ)).map g).f q))

/- The reusable comparison principle underlying Lemma 12.25.4: a columnwise quasi-isomorphism
between finitely supported double complexes induces a quasi-isomorphism on total complexes. -/
#check (HomologicalComplex₂.Total.Map.quasiIso_of_columnwise hA hB g hgColumn :
  QuasiIso (HomologicalComplex₂.total.map g (up ℤ)))

/- The same reusable comparison principle in the rowwise orientation. -/
#check (HomologicalComplex₂.Total.Map.quasiIso_of_rowwise hA hB g hgRow :
  QuasiIso (HomologicalComplex₂.total.map g (up ℤ)))

end TotalMap

section ZeroRow

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
variable [A.HasTotal (up ℤ)]
variable (hfin : HomologicalComplex₂.AntidiagonalSupport.Finite A)
variable (f : K ⟶ A.zeroRow)
variable (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0)
variable (p q : ℤ)
variable (hvanish : ∀ p q : ℤ, q < 0 → IsZero ((A.X p).X q))
variable (hexact : ∀ p q : ℤ, 0 < q → (A.X p).ExactAt q)
variable (hexactAll : ∀ p q : ℤ, q ≠ 0 → (A.X p).ExactAt q)
variable (hfCycles : ∀ p : ℤ, IsIso (HomologicalComplex₂.ZeroRow.Cycles.map f hf p))
variable (hfHomology : ∀ p : ℤ, IsIso (HomologicalComplex₂.ZeroRow.Homology.map f hf p))

/- Lemma 12.25.4 [0133]: the component maps into the zeroth row induce a map to the total
complex. -/
#check (HomologicalComplex₂.ZeroRow.ToTotal.map f hf : K ⟶ A.total (up ℤ))

/- Lemma 12.25.4 [0133]: the induced maps to vertical cycles express the degreewise isomorphism
hypothesis. -/
#check (HomologicalComplex₂.ZeroRow.Cycles.map f hf p : K.X p ⟶ (A.X p).cycles 0)

/- The reusable comparison criterion is naturally stated using the induced maps to degree-zero
vertical homology; this avoids imposing the source's stronger negative-vanishing hypothesis. -/
#check (HomologicalComplex₂.ZeroRow.Homology.map f hf p : K.X p ⟶ (A.X p).homology 0)

/- The library-facing zeroth-row criterion only needs transverse exactness and isomorphisms on
degree-zero vertical homology. -/
#check (HomologicalComplex₂.ZeroRow.ToTotal.quasiIso_of_exact hfin
  hexactAll
  f hf hfHomology : QuasiIso (HomologicalComplex₂.ZeroRow.ToTotal.map f hf))

/- Lemma 12.25.4 [0133]: under finite antidiagonal support, vanishing below the zeroth row,
exactness above it, and the cycle isomorphisms, the comparison is a quasi-isomorphism. -/
@[stacks 0133]
#check (HomologicalComplex₂.ZeroRow.ToTotal.quasiIso_of_vanish_below
  hfin hvanish hexact f hf hfCycles : QuasiIso (HomologicalComplex₂.ZeroRow.ToTotal.map f hf))

end ZeroRow

section ZeroColumn

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
variable [A.HasTotal (up ℤ)]
variable (hfin : HomologicalComplex₂.AntidiagonalSupport.Finite A)
variable (f : K ⟶ A.zeroColumn)
variable (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0)
variable (p q : ℤ)
variable (hvanish : ∀ p q : ℤ, p < 0 → IsZero ((A.X p).X q))
variable (hexact : ∀ q p : ℤ, 0 < p → (A.flip.X q).ExactAt p)
variable (hexactAll : ∀ q p : ℤ, p ≠ 0 → (A.flip.X q).ExactAt p)
variable (hfCycles : ∀ q : ℤ, IsIso (HomologicalComplex₂.ZeroColumn.Cycles.map f hf q))
variable (hfHomology : ∀ q : ℤ, IsIso (HomologicalComplex₂.ZeroColumn.Homology.map f hf q))

/- Lemma 12.25.4, symmetric variant [0133]: the component maps into the zeroth column induce a
map to the total complex. -/
#check (HomologicalComplex₂.ZeroColumn.ToTotal.map f hf : K ⟶ A.total (up ℤ))

/- Lemma 12.25.4, symmetric variant [0133]: the induced maps to horizontal cycles express the
degreewise isomorphism hypothesis. -/
#check (HomologicalComplex₂.ZeroColumn.Cycles.map f hf q : K.X q ⟶ (A.flip.X q).cycles 0)

/- The symmetric reusable criterion uses the induced maps to degree-zero horizontal homology. -/
#check (HomologicalComplex₂.ZeroColumn.Homology.map f hf q : K.X q ⟶ (A.flip.X q).homology 0)

/- The symmetric library-facing criterion is stated on degree-zero horizontal homology. -/
#check (HomologicalComplex₂.ZeroColumn.ToTotal.quasiIso_of_exact hfin
  hexactAll
  f hf hfHomology : QuasiIso (HomologicalComplex₂.ZeroColumn.ToTotal.map f hf))

/- Lemma 12.25.4, symmetric variant [0133]: under the exchanged hypotheses the zeroth-column
comparison is a quasi-isomorphism. -/
@[stacks 0133]
#check (HomologicalComplex₂.ZeroColumn.ToTotal.quasiIso_of_vanish_left
  hfin hvanish hexact f hf hfCycles :
  QuasiIso (HomologicalComplex₂.ZeroColumn.ToTotal.map f hf))

end ZeroColumn
