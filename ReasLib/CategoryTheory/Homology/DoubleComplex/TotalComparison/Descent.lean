module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison

/-!
# Comparison Maps from a Total Complex to an Axis

This file constructs the maps dual in direction to the axis-to-total comparisons in
`DoubleComplex/TotalComparison`.  A map out of the zeroth row or zeroth column extends over the
coproduct total precisely when it kills the differential entering that axis.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex
open scoped HomologicalComplex₂

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace ZeroColumn

namespace FromTotal

/-- The degree-`n` component of the map from a total complex to its zeroth column. -/
noncomputable def component
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : A.zeroColumn ⟶ K) (n : ℤ) :
    (A.total (up ℤ)).X n ⟶ K.X n :=
  A.totalDesc fun p q h ↦
    if hp : p = 0 then
      (HomologicalComplex₂.XXIsoOfEq C (up ℤ) (up ℤ) A hp rfl).hom ≫
        f.f q ≫
          (K.XIsoOfEq
            (Eq.trans (Int.zero_add q).symm
              (Eq.trans (congrArg (fun p : ℤ ↦ p + q) hp).symm h))).hom
    else
      0

/-- The zeroth-column descent components commute with differentials when the column map kills the
horizontal differential entering degree zero. -/
theorem comm
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : A.zeroColumn ⟶ K) (hf : A.d (-1) 0 ≫ f = 0)
    (n n' : ℤ) (hnn' : (up ℤ).Rel n n') :
    component f n ≫ K.d n n' =
      (A.total (up ℤ)).d n n' ≫ component f n' := sorry

/-- A map out of the zeroth column that kills the incoming horizontal differential induces a
canonical map out of the coproduct total complex. -/
@[stacks 09IZ "the comparison map from a total complex to its zeroth column"]
noncomputable def map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : A.zeroColumn ⟶ K) (hf : A.d (-1) 0 ≫ f = 0) :
    A.total (up ℤ) ⟶ K where
  f := component f
  comm' := comm f hf

/-- Precomposing the zeroth-column descent with an antidiagonal inclusion recovers the prescribed
column map in horizontal degree zero and is zero on every other column. -/
@[reassoc]
theorem ι_map_f
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : A.zeroColumn ⟶ K) (hf : A.d (-1) 0 ≫ f = 0)
    (p q n : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = n) :
    A.ιTotal (up ℤ) p q n h ≫ (map f hf).f n =
      if hp : p = 0 then
        (HomologicalComplex₂.XXIsoOfEq C (up ℤ) (up ℤ) A hp rfl).hom ≫
          f.f q ≫ (K.XIsoOfEq (ZeroColumn.index_eq hp h)).hom
      else
        0 := sorry

/-- The total-to-zeroth-column comparison is independent of the proof of the incoming-differential
condition. -/
theorem proof_irrel
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : A.zeroColumn ⟶ K)
    (hf hf' : A.d (-1) 0 ≫ f = 0) :
    map f hf = map f hf' := sorry

end FromTotal

end ZeroColumn

namespace ZeroRow

namespace FromTotal

/-- The degree-`n` component of the map from a total complex to its zeroth row. -/
noncomputable def component
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : A.zeroRow ⟶ K) (n : ℤ) :
    (A.total (up ℤ)).X n ⟶ K.X n :=
  ((A.totalFlipIso (up ℤ)).inv).f n ≫ ZeroColumn.FromTotal.component f n

/-- The zeroth-row descent components commute with differentials when the row map kills the
vertical differential entering degree zero. -/
theorem comm
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : A.zeroRow ⟶ K) (hf : A.flip.d (-1) 0 ≫ f = 0)
    (n n' : ℤ) (hnn' : (up ℤ).Rel n n') :
    component f n ≫ K.d n n' =
      (A.total (up ℤ)).d n n' ≫ component f n' := sorry

/-- A map out of the zeroth row that kills the incoming vertical differentials induces a
canonical map out of the coproduct total complex. -/
@[stacks 09IZ "the comparison map from a total complex to its zeroth row"]
noncomputable def map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : A.zeroRow ⟶ K) (hf : A.flip.d (-1) 0 ≫ f = 0) :
    A.total (up ℤ) ⟶ K where
  f := component f
  comm' := comm f hf

/-- Precomposing the zeroth-row descent with an antidiagonal inclusion recovers the prescribed
row map in vertical degree zero and is zero on every other row. -/
theorem ι_map_f
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : A.zeroRow ⟶ K) (hf : A.flip.d (-1) 0 ≫ f = 0)
    (p q n : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = n) :
    A.ιTotal (up ℤ) p q n h ≫ (map f hf).f n =
      if hq : q = 0 then
        (HomologicalComplex₂.XXIsoOfEq C (up ℤ) (up ℤ) A rfl hq).hom ≫
          f.f p ≫ (K.XIsoOfEq (ZeroRow.index_eq hq h)).hom
      else
        0 := sorry

/-- The total-to-zeroth-row comparison is independent of the proof of its componentwise
incoming-differential condition. -/
theorem proof_irrel
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : A.zeroRow ⟶ K)
    (hf hf' : A.flip.d (-1) 0 ≫ f = 0) :
    map f hf = map f hf' := sorry

end FromTotal

end ZeroRow

end HomologicalComplex₂
