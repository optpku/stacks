/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison.Descent

/-!
# Product Total Complexes

@stack 09J0
@stack 0E1R

The product total of a cohomological double complex is constructed by totalizing the transported
opposite double complex and then returning across the cochain-complex opposite equivalence.  This
representation reuses mathlib's total-complex differential and exposes the canonical comparisons
from the product total to the zeroth row and zeroth column.  Its degreewise product structure is
exposed by the antidiagonal projections `ProductTotal.π` and their extensionality API.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape HomologicalComplex Opposite
open scoped HomologicalComplex₂

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace ProductTotal

/-- The opposite of a cohomological double complex, viewed as a cochain complex of opposite
cochain complexes. -/
abbrev cochainOp (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    CochainComplex (CochainComplex C ℤ)ᵒᵖ ℤ :=
  (ChainComplex.cochainComplexEquivalence ((CochainComplex C ℤ)ᵒᵖ)).functor.obj K.op

/-- The transported opposite double complex whose coproduct total represents the product total
of `K`. -/
abbrev opBicomplex (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    HomologicalComplex₂ Cᵒᵖ (up ℤ) (up ℤ) :=
  (((CochainComplex.opEquivalence C).functor).mapHomologicalComplex (up ℤ)).obj
    (cochainOp K)

/-- A double complex has a product total when the transported opposite double complex has the
coproduct total used to construct it. This is the objectwise existence hypothesis dual to
`HomologicalComplex₂.HasTotal`. -/
@[stacks 09J0 "objectwise existence of a product total complex"]
abbrev HasTotal (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) : Prop :=
  (opBicomplex K).HasTotal (up ℤ)

/-- Existence of a product total is invariant under isomorphism of double complexes. -/
@[stacks 09J0 "product-total existence is invariant under isomorphism"]
theorem hasTotal_of_iso {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (e : K ≅ L) [HasTotal K] : HasTotal L := sorry

/-- The coproduct total in the opposite category that represents the product total of `K`. -/
abbrev op (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [HasTotal K] :
    CochainComplex Cᵒᵖ ℤ :=
  (opBicomplex K).total (up ℤ)

/-- The product total complex of a cohomological double complex. -/
@[stacks 09J0 "product total complex of a double complex"]
abbrev complex (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [HasTotal K] :
    CochainComplex C ℤ :=
  ((CochainComplex.opEquivalence C).inverse.obj (op K)).unop

/-- The projection from degree `p + q` of a product total complex to the `(p,q)` component of the
double complex.  This is dual to `HomologicalComplex₂.ιTotal` and is the canonical entry point for
the degreewise product universal property. -/
@[stacks 09J0 "antidiagonal projection from a product total complex"]
noncomputable def π (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [HasTotal K]
    (p q : ℤ) :
    (complex K).X (p + q) ⟶ (K.X p).X q :=
  ((opBicomplex K).ιTotal (up ℤ) (-p) (-q) (-(p + q))
      ((add_comm (-p) (-q)).trans (neg_add_rev p q).symm)).unop ≫
    (HomologicalComplex₂.XXIsoOfEq C (up ℤ) (up ℤ) K
      (Int.neg_neg p) (Int.neg_neg q)).hom

/-- The antidiagonal projection written at an equal total degree. -/
@[stacks 09J0 "antidiagonal projection at an identified total degree"]
noncomputable def πOfEq (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [HasTotal K]
    (p q : ℤ) {n : ℤ} (h : p + q = n) :
    (complex K).X n ⟶ (K.X p).X q :=
  ((complex K).XIsoOfEq h.symm).hom ≫ π K p q

/-- The transported antidiagonal projection is independent of the proof identifying its total
degree. -/
theorem πOfEq_proof_irrel (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [HasTotal K]
    (p q n : ℤ) (h h' : p + q = n) :
    πOfEq K p q h = πOfEq K p q h' := sorry

/-- Maps into one degree of a product total complex are determined by all antidiagonal
projections. -/
@[ext]
theorem π_hom_ext (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [HasTotal K]
    {n : ℤ} {X : C} (f g : X ⟶ (complex K).X n)
    (hfg : ∀ (p q : ℤ) (h : p + q = n),
      f ≫ πOfEq K p q h = g ≫ πOfEq K p q h) :
    f = g := sorry

/-- The functor from cohomological double complexes to their product total complexes. -/
@[stacks 09J0 "product-total functor"]
abbrev functor [HasCountableProducts C] :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ CochainComplex C ℤ :=
  opOp _ ⋙
    ((HomologicalComplex.opFunctor (CochainComplex C ℤ) (up ℤ)) ⋙
      (ChainComplex.cochainComplexEquivalence ((CochainComplex C ℤ)ᵒᵖ)).functor ⋙
      ((CochainComplex.opEquivalence C).functor).mapHomologicalComplex (up ℤ) ⋙
      HomologicalComplex₂.totalFunctor Cᵒᵖ (up ℤ) (up ℤ) (up ℤ) ⋙
      (CochainComplex.opEquivalence C).inverse).leftOp

/-- Evaluation of the product-total functor agrees with the named product-total construction. -/
theorem functor_obj [HasCountableProducts C]
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    (functor (C := C)).obj K = complex K := sorry

/-- Product-total maps commute with the canonical antidiagonal projections. -/
@[reassoc]
theorem map_f_π [HasCountableProducts C]
    {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L) (p q : ℤ) :
    ((functor (C := C)).map f).f (p + q) ≫ π L p q =
      π K p q ≫ (f.f p).f q := sorry

/-- The cochain complex in the opposite category canonically associated to a cochain complex. -/
abbrev opComplex (K : CochainComplex C ℤ) : CochainComplex Cᵒᵖ ℤ :=
  (CochainComplex.opEquivalence C).functor.obj (Opposite.op K)

/-- A map from the zeroth column of `A` becomes a map to the zeroth column of the opposite double
complex representing `ProductTotal.complex A`. -/
abbrev ZeroColumn.FromTotal.opMap
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : A.zeroColumn ⟶ K) :
    opComplex K ⟶ (opBicomplex A).zeroColumn :=
  (CochainComplex.opEquivalence C).functor.map f.op

/-- Killing the horizontal differential entering the zeroth column is transported to the
horizontal cycle condition required by the opposite-side zeroth-column comparison. -/
theorem ZeroColumn.FromTotal.opMap_cycles
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : A.zeroColumn ⟶ K) (hf : A.d (-1) 0 ≫ f = 0) :
    ∀ q : ℤ, (ZeroColumn.FromTotal.opMap f).f q ≫ ((opBicomplex A).d 0 1).f q = 0 := sorry

/-- The degree-`n` component of the opposite-side comparison from a product total to the zeroth
column. -/
@[stacks 0E1R "product-total zeroth-column comparison component"]
noncomputable def ZeroColumn.FromTotal.opComponent
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroColumn ⟶ K) (n : ℤ) :
    (opComplex K).X n ⟶ (op A).X n :=
  HomologicalComplex₂.ZeroColumn.ToTotal.component (ZeroColumn.FromTotal.opMap f) n

/-- The opposite-side zeroth-column comparison components commute with differentials under the
incoming horizontal-differential condition. -/
theorem ZeroColumn.FromTotal.opComm
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroColumn ⟶ K) (hf : A.d (-1) 0 ≫ f = 0)
    (n n' : ℤ) (hnn' : (up ℤ).Rel n n') :
    opComponent f n ≫ (op A).d n n' =
      (opComplex K).d n n' ≫ opComponent f n' := sorry

/-- The opposite-side map whose transport is the canonical comparison from a product total to
the zeroth column. -/
noncomputable def ZeroColumn.FromTotal.op
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroColumn ⟶ K) (hf : A.d (-1) 0 ≫ f = 0) :
    opComplex K ⟶ op A where
  f := opComponent f
  comm' := opComm f hf

/-- The opposite-side zeroth-column comparison has the expected inclusion into the `(0,n)`
antidiagonal summand. -/
@[simp]
theorem ZeroColumn.FromTotal.op_f
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroColumn ⟶ K) (hf : A.d (-1) 0 ≫ f = 0) (n : ℤ) :
    (ZeroColumn.FromTotal.op f hf).f n =
      (ZeroColumn.FromTotal.opMap f).f n ≫
        (opBicomplex A).ιTotal (up ℤ) 0 n n (Int.zero_add n) := sorry

/-- A map from the zeroth row of `A` becomes a map to the zeroth row of the opposite double
complex representing `ProductTotal.complex A`. -/
abbrev ZeroRow.FromTotal.opMap
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : A.zeroRow ⟶ K) :
    opComplex K ⟶ (opBicomplex A).zeroRow :=
  (CochainComplex.opEquivalence C).functor.map f.op

/-- Killing the vertical differential entering the zeroth row is transported to the vertical
cycle condition required by the opposite-side zeroth-row comparison. -/
theorem ZeroRow.FromTotal.opMap_cycles
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : A.zeroRow ⟶ K) (hf : A.flip.d (-1) 0 ≫ f = 0) :
    ∀ p : ℤ, (ZeroRow.FromTotal.opMap f).f p ≫ ((opBicomplex A).X p).d 0 1 = 0 := sorry

/-- The degree-`n` component of the opposite-side comparison from a product total to the zeroth
row. -/
@[stacks 0E1R "product-total zeroth-row comparison component"]
noncomputable def ZeroRow.FromTotal.opComponent
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroRow ⟶ K) (n : ℤ) :
    (opComplex K).X n ⟶ (op A).X n :=
  HomologicalComplex₂.ZeroRow.ToTotal.component (ZeroRow.FromTotal.opMap f) n

/-- The opposite-side zeroth-row comparison components commute with differentials under the
incoming vertical-differential condition. -/
theorem ZeroRow.FromTotal.opComm
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroRow ⟶ K) (hf : A.flip.d (-1) 0 ≫ f = 0)
    (n n' : ℤ) (hnn' : (up ℤ).Rel n n') :
    opComponent f n ≫ (op A).d n n' =
      (opComplex K).d n n' ≫ opComponent f n' := sorry

/-- The opposite-side map whose transport is the canonical comparison from a product total to
the zeroth row. -/
noncomputable def ZeroRow.FromTotal.op
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroRow ⟶ K) (hf : A.flip.d (-1) 0 ≫ f = 0) :
    opComplex K ⟶ op A where
  f := opComponent f
  comm' := opComm f hf

/-- The opposite-side zeroth-row comparison has the expected inclusion into the `(n,0)`
antidiagonal summand. -/
@[simp]
theorem ZeroRow.FromTotal.op_f
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroRow ⟶ K) (hf : A.flip.d (-1) 0 ≫ f = 0) (n : ℤ) :
    (ZeroRow.FromTotal.op f hf).f n =
      (ZeroRow.FromTotal.opMap f).f n ≫
        (opBicomplex A).ιTotal (up ℤ) n 0 n (Int.add_zero n) := sorry

/-- A map into the zeroth column of `A` becomes a map out of the zeroth column of the opposite
double complex representing `ProductTotal.complex A`. -/
abbrev ZeroColumn.ToTotal.opMap
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn) :
    (opBicomplex A).zeroColumn ⟶ opComplex K :=
  (CochainComplex.opEquivalence C).functor.map f.op

/-- The condition that a map into the zeroth column is killed by the outgoing horizontal
differential becomes the incoming-differential condition for the opposite double complex. -/
theorem ZeroColumn.ToTotal.opMap_comp_zero
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroColumn) (hf : f ≫ A.d 0 1 = 0) :
    (opBicomplex A).d (-1) 0 ≫ ZeroColumn.ToTotal.opMap f = 0 := sorry

/-- The degree-`n` component of the opposite-side descent from the zeroth column to a product
total. -/
@[stacks 09J0 "zeroth-column product-total descent component"]
noncomputable def ZeroColumn.ToTotal.opComponent
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroColumn) (n : ℤ) :
    (op A).X n ⟶ (opComplex K).X n :=
  HomologicalComplex₂.ZeroColumn.FromTotal.component (ZeroColumn.ToTotal.opMap f) n

/-- The opposite-side zeroth-column descent components commute with differentials under the
outgoing horizontal-differential condition. -/
theorem ZeroColumn.ToTotal.opComm
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroColumn) (hf : f ≫ A.d 0 1 = 0)
    (n n' : ℤ) (hnn' : (up ℤ).Rel n n') :
    opComponent f n ≫ (opComplex K).d n n' =
      (op A).d n n' ≫ opComponent f n' := sorry

/-- The opposite-side descent map whose transport is the canonical comparison from the zeroth
column to a product total. -/
noncomputable def ZeroColumn.ToTotal.op
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroColumn) (hf : f ≫ A.d 0 1 = 0) :
    op A ⟶ opComplex K where
  f := opComponent f
  comm' := opComm f hf

/-- On each antidiagonal summand, the opposite-side descent from the zeroth column is the
prescribed map in horizontal degree zero and zero in every other horizontal degree. -/
@[reassoc]
theorem ZeroColumn.ToTotal.ιTotal_op_f
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroColumn) (hf : f ≫ A.d 0 1 = 0)
    (p q n : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = n) :
    (opBicomplex A).ιTotal (up ℤ) p q n h ≫
        (ZeroColumn.ToTotal.op f hf).f n =
      if hp : p = 0 then
        (HomologicalComplex₂.XXIsoOfEq Cᵒᵖ (up ℤ) (up ℤ)
            (opBicomplex A) hp rfl).hom ≫
          (ZeroColumn.ToTotal.opMap f).f q ≫
            ((opComplex K).XIsoOfEq (ZeroColumn.index_eq hp h)).hom
      else
        0 := sorry

/-- A map into the zeroth row of `A` becomes a map out of the zeroth row of the opposite double
complex representing `ProductTotal.complex A`. -/
abbrev ZeroRow.ToTotal.opMap
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroRow) :
    (opBicomplex A).zeroRow ⟶ opComplex K :=
  (CochainComplex.opEquivalence C).functor.map f.op

/-- The condition that a map into the zeroth row is killed by the outgoing vertical differential
becomes the incoming-differential condition for the flipped opposite double complex. -/
theorem ZeroRow.ToTotal.opMap_comp_zero
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ A.zeroRow) (hf : f ≫ A.flip.d 0 1 = 0) :
    (opBicomplex A).flip.d (-1) 0 ≫ ZeroRow.ToTotal.opMap f = 0 := sorry

/-- The degree-`n` component of the opposite-side descent from the zeroth row to a product
total. -/
@[stacks 09J0 "zeroth-row product-total descent component"]
noncomputable def ZeroRow.ToTotal.opComponent
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroRow) (n : ℤ) :
    (op A).X n ⟶ (opComplex K).X n :=
  HomologicalComplex₂.ZeroRow.FromTotal.component (ZeroRow.ToTotal.opMap f) n

/-- The opposite-side zeroth-row descent components commute with differentials under the
outgoing vertical-differential condition. -/
theorem ZeroRow.ToTotal.opComm
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroRow) (hf : f ≫ A.flip.d 0 1 = 0)
    (n n' : ℤ) (hnn' : (up ℤ).Rel n n') :
    opComponent f n ≫ (opComplex K).d n n' =
      (op A).d n n' ≫ opComponent f n' := sorry

/-- The opposite-side descent map whose transport is the canonical comparison from the zeroth row
to a product total. -/
noncomputable def ZeroRow.ToTotal.op
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroRow) (hf : f ≫ A.flip.d 0 1 = 0) :
    op A ⟶ opComplex K where
  f := opComponent f
  comm' := opComm f hf

/-- On each antidiagonal summand, the opposite-side descent from the zeroth row is the prescribed
map in vertical degree zero and zero in every other vertical degree. -/
@[reassoc]
theorem ZeroRow.ToTotal.ιTotal_op_f
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroRow) (hf : f ≫ A.flip.d 0 1 = 0)
    (p q n : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = n) :
    (opBicomplex A).ιTotal (up ℤ) p q n h ≫
        (ZeroRow.ToTotal.op f hf).f n =
      if hq : q = 0 then
        (HomologicalComplex₂.XXIsoOfEq Cᵒᵖ (up ℤ) (up ℤ)
            (opBicomplex A) rfl hq).hom ≫
          (ZeroRow.ToTotal.opMap f).f p ≫
            ((opComplex K).XIsoOfEq (ZeroRow.index_eq hq h)).hom
      else
        0 := sorry

/-- A map out of the zeroth column that kills its incoming horizontal differential induces a
canonical map from the product total complex. -/
@[stacks 0E1R "the comparison map from a product total to its zeroth column"]
noncomputable def ZeroColumn.FromTotal.map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroColumn ⟶ K) (hf : A.d (-1) 0 ≫ f = 0) :
    complex A ⟶ K :=
  (((CochainComplex.opEquivalence C).inverse.map (ZeroColumn.FromTotal.op f hf))).unop ≫
    (((CochainComplex.opEquivalence C).unitIso.app (Opposite.op K)).unop).hom

/-- After passing to the opposite category, the product-total-to-zeroth-column comparison is the
canonical opposite-side comparison, preceded only by the unit of the cochain-complex opposite
equivalence. -/
theorem ZeroColumn.FromTotal.map_op
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroColumn ⟶ K) (hf : A.d (-1) 0 ≫ f = 0) :
    (ZeroColumn.FromTotal.map f hf).op =
      (CochainComplex.opEquivalence C).unitIso.hom.app (Opposite.op K) ≫
        (CochainComplex.opEquivalence C).inverse.map
          (ZeroColumn.FromTotal.op f hf) := sorry

/-- The product-total-to-zeroth-column comparison is independent of the proof of the incoming
differential condition. -/
theorem ZeroColumn.FromTotal.map_proof_irrel
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroColumn ⟶ K) (hf hf' : A.d (-1) 0 ≫ f = 0) :
    ZeroColumn.FromTotal.map f hf = ZeroColumn.FromTotal.map f hf' := sorry

/-- A map out of the zeroth row that kills its incoming vertical differential induces a
canonical map from the product total complex. -/
@[stacks 0E1R "the comparison map from a product total to its zeroth row"]
noncomputable def ZeroRow.FromTotal.map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroRow ⟶ K) (hf : A.flip.d (-1) 0 ≫ f = 0) :
    complex A ⟶ K :=
  (((CochainComplex.opEquivalence C).inverse.map (ZeroRow.FromTotal.op f hf))).unop ≫
    (((CochainComplex.opEquivalence C).unitIso.app (Opposite.op K)).unop).hom

/-- After passing to the opposite category, the product-total-to-zeroth-row comparison is the
canonical opposite-side comparison, preceded only by the unit of the cochain-complex opposite
equivalence. -/
theorem ZeroRow.FromTotal.map_op
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroRow ⟶ K) (hf : A.flip.d (-1) 0 ≫ f = 0) :
    (ZeroRow.FromTotal.map f hf).op =
      (CochainComplex.opEquivalence C).unitIso.hom.app (Opposite.op K) ≫
        (CochainComplex.opEquivalence C).inverse.map
          (ZeroRow.FromTotal.op f hf) := sorry

/-- The product-total-to-zeroth-row comparison is independent of the proof of its incoming
differential condition. -/
theorem ZeroRow.FromTotal.map_proof_irrel
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : A.zeroRow ⟶ K) (hf hf' : A.flip.d (-1) 0 ≫ f = 0) :
    ZeroRow.FromTotal.map f hf = ZeroRow.FromTotal.map f hf' := sorry

/-- A map into the zeroth column that is killed by its outgoing horizontal differential induces a
canonical map into the product total complex. -/
@[stacks 09J0 "the comparison map from the zeroth column to a product total"]
noncomputable def ZeroColumn.ToTotal.map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroColumn) (hf : f ≫ A.d 0 1 = 0) :
    K ⟶ complex A :=
  (((CochainComplex.opEquivalence C).unitIso.app (Opposite.op K)).unop).inv ≫
    (((CochainComplex.opEquivalence C).inverse.map
      (ZeroColumn.ToTotal.op f hf))).unop

/-- Passing the zeroth-column-to-product-total comparison to the opposite category recovers the
canonical opposite-side descent, followed only by the inverse of the equivalence unit. -/
theorem ZeroColumn.ToTotal.map_op
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroColumn) (hf : f ≫ A.d 0 1 = 0) :
    (ZeroColumn.ToTotal.map f hf).op =
      (CochainComplex.opEquivalence C).inverse.map
          (ZeroColumn.ToTotal.op f hf) ≫
        (CochainComplex.opEquivalence C).unitIso.inv.app (Opposite.op K) := sorry

/-- The zeroth-column-to-product-total comparison is independent of the proof of the outgoing
differential condition. -/
theorem ZeroColumn.ToTotal.map_proof_irrel
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroColumn) (hf hf' : f ≫ A.d 0 1 = 0) :
    ZeroColumn.ToTotal.map f hf = ZeroColumn.ToTotal.map f hf' := sorry

/-- A map into the zeroth row that is killed by its outgoing vertical differential induces a
canonical map into the product total complex. -/
@[stacks 09J0 "the comparison map from the zeroth row to a product total"]
noncomputable def ZeroRow.ToTotal.map
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroRow) (hf : f ≫ A.flip.d 0 1 = 0) :
    K ⟶ complex A :=
  (((CochainComplex.opEquivalence C).unitIso.app (Opposite.op K)).unop).inv ≫
    (((CochainComplex.opEquivalence C).inverse.map
      (ZeroRow.ToTotal.op f hf))).unop

/-- Passing the zeroth-row-to-product-total comparison to the opposite category recovers the
canonical opposite-side descent, followed only by the inverse of the equivalence unit. -/
theorem ZeroRow.ToTotal.map_op
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroRow) (hf : f ≫ A.flip.d 0 1 = 0) :
    (ZeroRow.ToTotal.map f hf).op =
      (CochainComplex.opEquivalence C).inverse.map
          (ZeroRow.ToTotal.op f hf) ≫
        (CochainComplex.opEquivalence C).unitIso.inv.app (Opposite.op K) := sorry

/-- The zeroth-row-to-product-total comparison is independent of the proof of the outgoing
differential condition. -/
theorem ZeroRow.ToTotal.map_proof_irrel
    {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)} [HasTotal A]
    (f : K ⟶ A.zeroRow) (hf hf' : f ≫ A.flip.d 0 1 = 0) :
    ZeroRow.ToTotal.map f hf = ZeroRow.ToTotal.map f hf' := sorry

end ProductTotal

end HomologicalComplex₂
