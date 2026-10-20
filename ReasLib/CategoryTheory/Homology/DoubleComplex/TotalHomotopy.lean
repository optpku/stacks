module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison
public import ReasLib.CategoryTheory.Homology.DoubleComplex.BidegreeShift
public import ReasLib.CategoryTheory.Homology.Homotopy.CochainShift
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopies and total complexes

This file records that totalization in the first direction sends homotopies of bicomplex maps to
homotopies.  The construction is stated for arbitrary compatible complex shapes.  It also gives
the comparison between a cochain complex and the total complex of an outer degree-zero single
complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex

noncomputable section

universe v u w₁ w₂ w₁₂

namespace HomologicalComplex₂

namespace Total.Homotopy.First

section General

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
variable [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
variable {A B : HomologicalComplex₂ C c₁ c₂} [A.HasTotal c₁₂] [B.HasTotal c₁₂]

/-- The component family on total complexes induced by a degree `-1` family in the first
direction of a bicomplex. -/
noncomputable def component
    (h : ∀ i j, A.X i ⟶ B.X j) (k l : I₁₂) :
    (A.total c₁₂).X k ⟶ (B.total c₁₂).X l :=
  A.totalDesc fun i j _ ↦
    ComplexShape.ε₁ c₁ c₂ c₁₂ (c₁.prev i, j) •
      ((h i (c₁.prev i)).f j ≫ B.ιTotalOrZero c₁₂ (c₁.prev i) j l)

/-- On a total-complex summand, `component` is the corresponding first-direction
component followed by the target summand inclusion. -/
@[reassoc (attr := simp)]
theorem ι_component
    (h : ∀ i j, A.X i ⟶ B.X j) (i : I₁) (j : I₂) (k l : I₁₂)
    (hij : ComplexShape.π c₁ c₂ c₁₂ (i, j) = k) :
    A.ιTotal c₁₂ i j k hij ≫ component h k l =
      ComplexShape.ε₁ c₁ c₂ c₁₂ (c₁.prev i, j) •
        ((h i (c₁.prev i)).f j ≫ B.ιTotalOrZero c₁₂ (c₁.prev i) j l) := sorry

/-- The totalized component family vanishes outside predecessor total degrees. -/
theorem component_zero
    {f g : A ⟶ B} (h : Homotopy f g) (k l : I₁₂) (hkl : ¬ c₁₂.Rel l k) :
    component (c₁₂ := c₁₂) h.hom k l = 0 := sorry

/-- The totalized component family satisfies the homotopy identity. -/
theorem component_comm
    {f g : A ⟶ B} (h : Homotopy f g) (k : I₁₂) :
    (total.map f c₁₂).f k =
      dNext k (component (c₁₂ := c₁₂) h.hom) +
        prevD k (component (c₁₂ := c₁₂) h.hom) +
          (total.map g c₁₂).f k := sorry

/-- Totalization sends a homotopy in the first direction of a bicomplex to a homotopy of total
complex maps. -/
@[stacks 0G6B]
noncomputable def of {f g : A ⟶ B} (h : Homotopy f g) :
    Homotopy (total.map f c₁₂) (total.map g c₁₂) where
  hom := component (c₁₂ := c₁₂) h.hom
  zero := component_zero h
  comm := component_comm h

/-- Homotopic bicomplex maps induce homotopic maps on total complexes. -/
@[stacks 0G6B]
theorem homotopic {f g : A ⟶ B} (h : Homotopy f g) :
    homotopic C c₁₂ (total.map f c₁₂) (total.map g c₁₂) := sorry

/-- Homotopic bicomplex maps induce equal maps between total complexes in the homotopy
category. -/
@[stacks 0G6B]
theorem map_eq_in_homotopyCategory
    {f g : A ⟶ B} (h : Homotopy f g) :
    (HomotopyCategory.quotient C c₁₂).map (total.map f c₁₂) =
      (HomotopyCategory.quotient C c₁₂).map (total.map g c₁₂) := sorry

/-- Totalization sends an explicit homotopy equivalence of bicomplexes to an explicit homotopy
equivalence of total complexes. -/
noncomputable def equiv (e : HomotopyEquiv A B) :
    HomotopyEquiv (A.total c₁₂) (B.total c₁₂) where
  hom := total.map e.hom c₁₂
  inv := total.map e.inv c₁₂
  homotopyHomInvId :=
    (Homotopy.ofEq (total.map_comp e.hom e.inv c₁₂).symm).trans
      ((of e.homotopyHomInvId).trans
        (Homotopy.ofEq (total.map_id A c₁₂)))
  homotopyInvHomId :=
    (Homotopy.ofEq (total.map_comp e.inv e.hom c₁₂).symm).trans
      ((of e.homotopyInvHomId).trans
        (Homotopy.ofEq (total.map_id B c₁₂)))

/-- The total map of an explicit bicomplex homotopy equivalence belongs to the canonical
homotopy-equivalence morphism property. -/
theorem map_isHomotopyEquivalence (e : HomotopyEquiv A B) :
    homotopyEquivalences C c₁₂ (total.map e.hom c₁₂) := sorry

end General

section Shift

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A B : HomologicalComplex₂ C (up ℤ) (up ℤ)}
variable [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]

/-- Under the canonical identification of a self-homotopy with a map to the `(-1)`-shift,
totalization in the first direction agrees with the first-direction total-shift comparison. -/
@[stacks 0G6B]
theorem selfHomotopyToShift
    {f : A ⟶ B} (h : Homotopy f f) :
    CochainComplex.Homotopy.selfEquivShiftHom (total.map f (up ℤ)) (of h) =
      total.map (CochainComplex.Homotopy.selfEquivShiftHom f h) (up ℤ) ≫
        (B.totalShift₁Iso (-1)).hom := sorry

end Shift

end Total.Homotopy.First

namespace ZeroColumn.Single

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The degree-zero column map extracted from a map from the outer degree-zero single complex. -/
noncomputable def toColumn
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (a : (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M ⟶ A) :
    M ⟶ A.X 0 :=
  (singleObjXSelf (up ℤ) 0 M).inv ≫ a.f 0

/-- The column map extracted from an outer single-complex map lands in horizontal cycles. -/
theorem toColumn_comp_d
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (a : (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M ⟶ A)
    (q : ℤ) :
    (toColumn a).f q ≫ (A.d 0 1).f q = 0 := sorry

/-- The canonical comparison from a cochain complex to the total complex induced by a map from
its outer degree-zero single complex. -/
noncomputable def toTotal
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)]
    (a : (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M ⟶ A) :
    M ⟶ A.total (up ℤ) :=
  ZeroColumn.ToTotal.map (toColumn a) (toColumn_comp_d a)

/-- The single-zero comparison is the inclusion of the zeroth-column summand in each total
degree. -/
theorem toTotal_f
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)]
    (a : (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M ⟶ A) (n : ℤ) :
    (toTotal a).f n =
      (toColumn a).f n ≫
        A.ιTotal (up ℤ) 0 n n (ZeroColumn.totalDegree n) := sorry

/-- The single-zero comparison is natural in the target bicomplex. -/
theorem toTotal_comp
    {M : CochainComplex C ℤ} {A B : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)] [B.HasTotal (up ℤ)]
    (a : (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M ⟶ A) (f : A ⟶ B) :
    toTotal (a ≫ f) = toTotal a ≫ total.map f (up ℤ) := sorry

/-- The degree-zero column map extracted from a map to the outer degree-zero single complex. -/
noncomputable def fromColumn
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (b : A ⟶ (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M) :
    A.X 0 ⟶ M :=
  b.f 0 ≫ (singleObjXSelf (up ℤ) 0 M).hom

/-- The component of the comparison from a total complex to the complex underlying an outer
degree-zero single complex.  It is supported on the zero column. -/
noncomputable def fromTotalComponent
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)]
    (b : A ⟶ (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M) (n : ℤ) :
    (A.total (up ℤ)).X n ⟶ M.X n :=
  A.totalDesc fun p q h ↦
    if hp : p = 0 then
      (HomologicalComplex₂.XXIsoOfEq C (up ℤ) (up ℤ) A hp (rfl : q = q)).hom ≫
        (fromColumn b).f q ≫
          (M.XIsoOfEq
            (Eq.trans (Int.zero_add q).symm
              (Eq.trans (congrArg (fun p : ℤ ↦ p + q) hp).symm h))).hom
    else
      0

/-- Restricting `fromTotalComponent` to one summand exposes its zeroth-column branch. -/
theorem ι_fromTotalComponent
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)]
    (b : A ⟶ (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M)
    (p q n : ℤ) (h : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (p, q) = n) :
    A.ιTotal (up ℤ) p q n h ≫ fromTotalComponent b n =
      if hp : p = 0 then
        (HomologicalComplex₂.XXIsoOfEq C (up ℤ) (up ℤ) A hp (rfl : q = q)).hom ≫
          (fromColumn b).f q ≫
            (M.XIsoOfEq (ZeroColumn.index_eq hp h)).hom
      else
        0 := sorry

/-- The zero-column component family is compatible with the total differential. -/
theorem fromTotalComponent_comm
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)]
    (b : A ⟶ (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M)
    (n n' : ℤ) (hnn' : (up ℤ).Rel n n') :
    fromTotalComponent b n ≫ M.d n n' =
      (A.total (up ℤ)).d n n' ≫ fromTotalComponent b n' := sorry

/-- A map from a bicomplex to an outer degree-zero single complex induces a map from the total
complex to the underlying cochain complex. -/
noncomputable def fromTotal
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)]
    (b : A ⟶ (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M) :
    A.total (up ℤ) ⟶ M where
  f := fromTotalComponent b
  comm' := fromTotalComponent_comm b

/-- A homotopy to the identity on an outer degree-zero single complex makes the induced
single-to-total and total-to-single maps strict inverses on the underlying complex. -/
theorem toTotal_comp_fromTotal
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)]
    {a : (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M ⟶ A}
    {b : A ⟶ (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M}
    (h : Homotopy (a ≫ b)
      (𝟙 ((CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M))) :
    toTotal a ≫ fromTotal b = 𝟙 M := sorry

/-- The reverse single-zero comparison followed by the forward comparison is the totalization
of the corresponding bicomplex endomorphism. -/
theorem fromTotal_comp_toTotal
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)]
    (a : (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M ⟶ A)
    (b : A ⟶ (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M) :
    fromTotal b ≫ toTotal a = total.map (b ≫ a) (up ℤ) := sorry

/-- An explicit homotopy equivalence from an outer degree-zero single complex induces an
explicit homotopy equivalence from the underlying complex to the total complex. -/
noncomputable def homotopyEquiv
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)]
    (e : HomotopyEquiv
      ((CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M) A) :
    HomotopyEquiv M (A.total (up ℤ)) where
  hom := toTotal e.hom
  inv := fromTotal e.inv
  homotopyHomInvId :=
    Homotopy.ofEq (toTotal_comp_fromTotal e.homotopyHomInvId)
  homotopyInvHomId :=
    (Homotopy.ofEq (fromTotal_comp_toTotal e.hom e.inv)).trans
      ((Total.Homotopy.First.of e.homotopyInvHomId).trans
        (Homotopy.ofEq (total.map_id A (up ℤ))))

/-- Lemma 12.25.5 (general form): a homotopy-equivalence map from an outer degree-zero single
complex induces a homotopy-equivalence map from the underlying complex to the total complex. -/
@[stacks 0FKH]
theorem toTotal_isHomotopyEquivalence
    {M : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    [A.HasTotal (up ℤ)]
    {a : (CochainComplex.singleFunctor (CochainComplex C ℤ) 0).obj M ⟶ A}
    (ha : homotopyEquivalences (CochainComplex C ℤ) (up ℤ) a) :
    homotopyEquivalences C (up ℤ) (toTotal a) := sorry

end ZeroColumn.Single

end HomologicalComplex₂
