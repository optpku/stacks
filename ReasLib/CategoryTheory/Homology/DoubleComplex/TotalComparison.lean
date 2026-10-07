module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison Maps from an Axis to a Total Complex

@stack 0133

This file constructs the canonical maps from a complex mapping into the zeroth row or zeroth
column of a cohomological double complex to its total complex.  The construction only requires
the component maps to land in cycles.  Quasi-isomorphism criteria live in the higher
`TotalComparison/QuasiIso` leaf.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape HomologicalComplex
open scoped HomologicalComplex₂

noncomputable section

universe v u

namespace HomologicalComplex₂

section AxisFunctors

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- Evaluation of a cohomological double complex on its zeroth row. -/
abbrev zeroRowFunctor :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ CochainComplex C ℤ :=
  (HomologicalComplex.eval C (up ℤ) (0 : ℤ)).mapHomologicalComplex (up ℤ)

/-- Evaluation of a cohomological double complex on its zeroth column. -/
abbrev zeroColumnFunctor :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ CochainComplex C ℤ :=
  HomologicalComplex.eval (CochainComplex C ℤ) (up ℤ) (0 : ℤ)

/-- The zeroth row of a cohomological double complex. -/
abbrev zeroRow (A : HomologicalComplex₂ C (up ℤ) (up ℤ)) : CochainComplex C ℤ :=
  (zeroRowFunctor C).obj A

/-- The zeroth column of a cohomological double complex. -/
abbrev zeroColumn (A : HomologicalComplex₂ C (up ℤ) (up ℤ)) : CochainComplex C ℤ :=
  (zeroColumnFunctor C).obj A

namespace ZeroColumn

/-- The zeroth-column bidegree `(0,n)` has total degree `n`. -/
theorem totalDegree (n : ℤ) :
    ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (0, n) = n := sorry

/-- On an antidiagonal, a summand in horizontal degree zero has vertical degree equal to the
total degree. -/
theorem index_eq {p q n : ℤ} (hp : p = 0)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = n) : q = n := sorry

namespace ToFlipRow

/-- The componentwise identity maps commute with the differentials on the zeroth column of `A`
and the zeroth row of `A.flip`. -/
theorem comm
    (A : HomologicalComplex₂ C (up ℤ) (up ℤ)) (p q : ℤ) (hpq : (up ℤ).Rel p q) :
    (Iso.refl ((A.zeroColumn).X p)).hom ≫ (A.flip.zeroRow).d p q =
      (A.zeroColumn).d p q ≫ (Iso.refl ((A.zeroColumn).X q)).hom := sorry

/-- The zeroth column of `A` is canonically isomorphic to the zeroth row of `A.flip`. -/
noncomputable def iso
    (A : HomologicalComplex₂ C (up ℤ) (up ℤ)) : A.zeroColumn ≅ A.flip.zeroRow :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ ↦ Iso.refl _)
    (ZeroColumn.ToFlipRow.comm C A)

/-- The canonical zeroth-column/flip-row isomorphism is componentwise the identity. -/
@[simp]
theorem iso_hom_f
    (A : HomologicalComplex₂ C (up ℤ) (up ℤ)) (q : ℤ) :
    ((ZeroColumn.ToFlipRow.iso C A).hom.f q) = 𝟙 ((A.zeroColumn).X q) := sorry

end ToFlipRow

end ZeroColumn

namespace ZeroRow

/-- The zeroth-row bidegree `(n,0)` has total degree `n`. -/
theorem totalDegree (n : ℤ) :
    ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (n, 0) = n := sorry

/-- On an antidiagonal, a summand in vertical degree zero has horizontal degree equal to the
total degree. -/
theorem index_eq {p q n : ℤ} (hq : q = 0)
    (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = n) : p = n := sorry

end ZeroRow

end AxisFunctors

section ComparisonMaps

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace ZeroRow

namespace ToTotal

/-- The degree-`n` component of the map to the total complex induced from the zeroth row. -/
noncomputable def component
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : K ⟶ A.zeroRow) (n : ℤ) :
    K.X n ⟶ (A.total (up ℤ)).X n :=
  f.f n ≫ A.ιTotal (up ℤ) n 0 n (Int.add_zero n)

/-- The zeroth-row comparison components commute with the total differential when they land in
vertical cycles. -/
theorem comm
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : K ⟶ A.zeroRow)
    (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0)
    (n n' : ℤ) (hnn' : (up ℤ).Rel n n') :
    component f n ≫ (A.total (up ℤ)).d n n' =
      K.d n n' ≫ component f n' := sorry

/-- A map to the zeroth row whose components are vertical cycles induces a canonical map to the
total complex. -/
@[stacks 0133 "the comparison map from the zeroth row to the total complex"]
noncomputable def map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : K ⟶ A.zeroRow)
    (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0) :
    K ⟶ A.total (up ℤ) where
  f := component f
  comm' := comm f hf

/-- The components of the zeroth-row comparison map are the prescribed maps followed by the
corresponding total-complex inclusions. -/
@[simp]
theorem map_f
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : K ⟶ A.zeroRow)
    (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0) (n : ℤ) :
    (map f hf).f n =
      f.f n ≫ A.ιTotal (up ℤ) n 0 n (Int.add_zero n) := sorry

/-- The zeroth-row comparison map is independent of the proof of its cycle condition. -/
theorem proof_irrel
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : K ⟶ A.zeroRow)
    (hf hf' : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0) :
    map f hf = map f hf' := sorry

end ToTotal

end ZeroRow

namespace ZeroColumn

/-- A map to the zeroth column is killed by the outgoing horizontal differential exactly when
each component is a horizontal cycle. -/
theorem comp_d_eq_zero_iff
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn) :
    f ≫ A.d 0 1 = 0 ↔
      ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0 := sorry

namespace ToFlipRow

/-- A map to the zeroth column can be viewed as a map to the zeroth row after flipping the double
complex. -/
noncomputable def map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn) : K ⟶ A.flip.zeroRow :=
  f ≫ (ZeroColumn.ToFlipRow.iso C A).hom

/-- Viewing a zeroth-column map as a map to the flipped zeroth row does not change its
components. -/
@[simp]
theorem map_f
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn) (q : ℤ) :
    (map f).f q = f.f q := sorry

/-- A horizontal cycle condition on the zeroth column becomes the vertical cycle condition on the
zeroth row of the flipped double complex. -/
theorem cycles
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn) (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0) :
    ∀ q : ℤ, (map f).f q ≫ (A.flip.X q).d 0 1 = 0 := sorry

end ToFlipRow

namespace ToTotal

/-- The degree-`n` component of the map to the total complex induced from the zeroth column. -/
noncomputable def component
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : K ⟶ A.zeroColumn) (n : ℤ) :
    K.X n ⟶ (A.total (up ℤ)).X n :=
  f.f n ≫ A.ιTotal (up ℤ) 0 n n (Int.zero_add n)

/-- The zeroth-column comparison components commute with differentials when they land in
horizontal cycles. -/
theorem comm
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : K ⟶ A.zeroColumn)
    (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0)
    (n n' : ℤ) (hnn' : (up ℤ).Rel n n') :
    component f n ≫ (A.total (up ℤ)).d n n' =
      K.d n n' ≫ component f n' := sorry

/-- A map to the zeroth column whose components are horizontal cycles induces a canonical map to
the total complex. -/
@[stacks 0133 "the comparison map from the zeroth column to the total complex"]
noncomputable def map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : K ⟶ A.zeroColumn)
    (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0) :
    K ⟶ A.total (up ℤ) where
  f := component f
  comm' := comm f hf

/-- The components of the zeroth-column comparison map are the prescribed maps followed by the
corresponding total-complex inclusions. -/
@[simp]
theorem map_f
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : K ⟶ A.zeroColumn)
    (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0) (n : ℤ) :
    (map f hf).f n =
      f.f n ≫ A.ιTotal (up ℤ) 0 n n (Int.zero_add n) := sorry

/-- The zeroth-column comparison map is independent of the proof of its cycle condition. -/
theorem proof_irrel
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] (f : K ⟶ A.zeroColumn)
    (hf hf' : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0) :
    map f hf = map f hf' := sorry

end ToTotal

end ZeroColumn

end ComparisonMaps

section Naturality

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {K L : CochainComplex C ℤ}
variable {A B : HomologicalComplex₂ C (up ℤ) (up ℤ)}

namespace ZeroRow

namespace ToTotal

/-- Precomposition preserves the vertical cycle condition on the zeroth row. -/
theorem precomp_cycles
    (e : L ⟶ K) (f : K ⟶ A.zeroRow)
    (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0) :
    ∀ p : ℤ, (e ≫ f).f p ≫ (A.X p).d 0 1 = 0 := sorry

/-- The zeroth-row comparison is natural under precomposition of its source complex. -/
theorem precomp
    [A.HasTotal (up ℤ)] (e : L ⟶ K) (f : K ⟶ A.zeroRow)
    (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0) :
    map (e ≫ f) (precomp_cycles e f hf) =
      e ≫ map f hf := sorry

/-- Postcomposition with a double-complex morphism preserves the vertical cycle condition on the
zeroth row. -/
theorem comp_cycles
    (f : K ⟶ A.zeroRow) (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0)
    (g : A ⟶ B) :
    ∀ p : ℤ, (f ≫ (zeroRowFunctor C).map g).f p ≫ (B.X p).d 0 1 = 0 := sorry

/-- The zeroth-row comparison is natural in the target double complex. -/
theorem naturality
    [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]
    (f : K ⟶ A.zeroRow) (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0)
    (g : A ⟶ B) :
    map (f ≫ (zeroRowFunctor C).map g) (comp_cycles f hf g) =
      map f hf ≫ HomologicalComplex₂.total.map g (up ℤ) := sorry

end ToTotal

end ZeroRow

namespace ZeroColumn

namespace ToTotal

/-- Precomposition preserves the horizontal cycle condition on the zeroth column. -/
theorem precomp_cycles
    (e : L ⟶ K) (f : K ⟶ A.zeroColumn)
    (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0) :
    ∀ q : ℤ, (e ≫ f).f q ≫ (A.d 0 1).f q = 0 := sorry

/-- The zeroth-column comparison is natural under precomposition of its source complex. -/
theorem precomp
    [A.HasTotal (up ℤ)] (e : L ⟶ K) (f : K ⟶ A.zeroColumn)
    (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0) :
    map (e ≫ f) (precomp_cycles e f hf) =
      e ≫ map f hf := sorry

/-- Postcomposition with a double-complex morphism preserves the horizontal cycle condition on
the zeroth column. -/
theorem comp_cycles
    (f : K ⟶ A.zeroColumn) (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0)
    (g : A ⟶ B) :
    ∀ q : ℤ, (f ≫ (zeroColumnFunctor C).map g).f q ≫ (B.d 0 1).f q = 0 := sorry

/-- The zeroth-column comparison is natural in the target double complex. -/
theorem naturality
    [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]
    (f : K ⟶ A.zeroColumn) (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0)
    (g : A ⟶ B) :
    map (f ≫ (zeroColumnFunctor C).map g) (comp_cycles f hf g) =
      map f hf ≫ HomologicalComplex₂.total.map g (up ℤ) := sorry

end ToTotal

end ZeroColumn

end Naturality

section HomologyData

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

namespace ZeroRow

namespace Cycles

/-- The map to vertical cycles induced by a cycle-compatible map to the zeroth row. -/
noncomputable def map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroRow) (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0) (p : ℤ) :
    K.X p ⟶ (A.X p).cycles 0 :=
  (A.X p).liftCycles' (f.f p) 1 rfl (hf p)

/-- The vertical-cycle lift recovers the original zeroth-row component after inclusion. -/
@[reassoc (attr := simp)]
theorem map_iCycles
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroRow) (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0) (p : ℤ) :
    map f hf p ≫ (A.X p).iCycles 0 = f.f p := sorry

end Cycles

end ZeroRow

namespace ZeroColumn

namespace Cycles

/-- The map to horizontal cycles induced by a zeroth-column map together with an explicit
cycle condition on the flipped double complex. -/
@[stacks 0133 "zeroth-column cycle lift with explicit flipped condition"]
noncomputable def mapOf
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn)
    (hf : ∀ q : ℤ, f.f q ≫ (A.flip.X q).d 0 1 = 0) (q : ℤ) :
    K.X q ⟶ (A.flip.X q).cycles 0 :=
  (A.flip.X q).liftCycles' (f.f q) 1 rfl (hf q)

/-- The explicit horizontal-cycle lift recovers the prescribed zeroth-column component after
inclusion. -/
@[reassoc (attr := simp)]
theorem mapOf_iCycles
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn)
    (hf : ∀ q : ℤ, f.f q ≫ (A.flip.X q).d 0 1 = 0) (q : ℤ) :
    mapOf f hf q ≫ (A.flip.X q).iCycles 0 = f.f q := sorry

/-- A horizontal cycle condition on a zeroth-column map gives the flipped cycle condition
required by `mapOf`. -/
theorem flip_cycles
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn) (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0) :
    ∀ q : ℤ, f.f q ≫ (A.flip.X q).d 0 1 = 0 := sorry

/-- The map to horizontal cycles induced by a cycle-compatible map to the zeroth column. -/
noncomputable def map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn) (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0) (q : ℤ) :
    K.X q ⟶ (A.flip.X q).cycles 0 :=
  mapOf f (flip_cycles f hf) q

/-- The horizontal-cycle lift recovers the flipped zeroth-row component after inclusion. -/
@[reassoc (attr := simp)]
theorem map_iCycles
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn) (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0) (q : ℤ) :
    map f hf q ≫ (A.flip.X q).iCycles 0 =
      (ZeroColumn.ToFlipRow.map f).f q := sorry

end Cycles

end ZeroColumn

namespace ZeroRow

namespace Homology

/-- The map on degree-zero vertical homology induced by a cycle-compatible map to the zeroth
row.  This is the canonical input for comparison theorems that do not assume negative vertical
degrees vanish. -/
noncomputable def map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroRow) (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0) (p : ℤ) :
    K.X p ⟶ (A.X p).homology 0 :=
  ZeroRow.Cycles.map f hf p ≫ (A.X p).homologyπ 0

end Homology

end ZeroRow

namespace ZeroColumn

namespace Homology

/-- The map on degree-zero horizontal homology induced by a zeroth-column map and an explicit
cycle condition on the flipped double complex. -/
@[stacks 0133 "zeroth-column homology map with explicit flipped condition"]
noncomputable def mapOf
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn)
    (hf : ∀ q : ℤ, f.f q ≫ (A.flip.X q).d 0 1 = 0) (q : ℤ) :
    K.X q ⟶ (A.flip.X q).homology 0 :=
  ZeroColumn.Cycles.mapOf f hf q ≫ (A.flip.X q).homologyπ 0

/-- The map on degree-zero horizontal homology induced by a cycle-compatible map to the zeroth
column. -/
noncomputable def map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn) (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0) (q : ℤ) :
    K.X q ⟶ (A.flip.X q).homology 0 :=
  mapOf f (ZeroColumn.Cycles.flip_cycles f hf) q

end Homology

end ZeroColumn

end HomologyData

end HomologicalComplex₂
