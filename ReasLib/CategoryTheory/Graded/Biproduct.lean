module

public import ReasLib.CategoryTheory.Graded.DegreeZero
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded direct sums

This leaf records split binary direct sums whose four structural maps have degree zero.
The same data simultaneously determine binary biproducts in the ambient graded category and in
its degree-zero wide subcategory.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe x w v u

namespace GradedCategory

section

variable {ι : Type x} [DecidableEq ι] [AddMonoid ι]
variable {R : Type w} [Semiring R] {C : Type u} [Category.{v} C] [Preadditive C]
variable [GradedCategory R C ι]

/-- Definition 22.25.4: a split binary direct sum in a graded category whose injections and
projections all have degree zero. -/
@[stacks 09P2]
structure IsGradedDirectSum {x y z : C} (i : x ⟶ z) (j : y ⟶ z) (p : z ⟶ x)
    (q : z ⟶ y) :
    Prop where
  /-- The first injection followed by the first projection is the identity. -/
  i_comp_p : i ≫ p = 𝟙 x
  /-- The first injection followed by the second projection vanishes. -/
  i_comp_q : i ≫ q = 0
  /-- The second injection followed by the first projection vanishes. -/
  j_comp_p : j ≫ p = 0
  /-- The second injection followed by the second projection is the identity. -/
  j_comp_q : j ≫ q = 𝟙 y
  /-- The two projection-injection composites sum to the identity. -/
  total : p ≫ i + q ≫ j = 𝟙 z
  /-- The first injection has degree zero. -/
  i_mem_homDegree_zero : i ∈ GradedCategory.homDegree (R := R) (ι := ι) x z 0
  /-- The second injection has degree zero. -/
  j_mem_homDegree_zero : j ∈ GradedCategory.homDegree (R := R) (ι := ι) y z 0
  /-- The first projection has degree zero. -/
  p_mem_homDegree_zero : p ∈ GradedCategory.homDegree (R := R) (ι := ι) z x 0
  /-- The second projection has degree zero. -/
  q_mem_homDegree_zero : q ∈ GradedCategory.homDegree (R := R) (ι := ι) z y 0

namespace IsGradedDirectSum

variable {x y z : C} {i : x ⟶ z} {j : y ⟶ z} {p : z ⟶ x} {q : z ⟶ y}

/-- The degree-zero bicone determined by graded direct-sum data. -/
def degreeZeroBicone (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    BinaryBicone (⟨x⟩ : DegreeZero (R := R) C ι) (⟨y⟩ : DegreeZero (R := R) C ι) where
  pt := ⟨z⟩
  fst := ⟨p, hds.p_mem_homDegree_zero⟩
  snd := ⟨q, hds.q_mem_homDegree_zero⟩
  inl := ⟨i, hds.i_mem_homDegree_zero⟩
  inr := ⟨j, hds.j_mem_homDegree_zero⟩
  inl_fst := sorry
  inl_snd := sorry
  inr_fst := sorry
  inr_snd := sorry

/-- The first projection of the degree-zero bicone is the supplied projection. -/
@[simp]
theorem degreeZeroBicone_fst (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    (degreeZeroBicone hds).fst.hom = p := sorry

/-- The second projection of the degree-zero bicone is the supplied projection. -/
@[simp]
theorem degreeZeroBicone_snd (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    (degreeZeroBicone hds).snd.hom = q := sorry

/-- The first injection of the degree-zero bicone is the supplied injection. -/
@[simp]
theorem degreeZeroBicone_inl (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    (degreeZeroBicone hds).inl.hom = i := sorry

/-- The second injection of the degree-zero bicone is the supplied injection. -/
@[simp]
theorem degreeZeroBicone_inr (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    (degreeZeroBicone hds).inr.hom = j := sorry

/-- The product comparison map into the degree-zero bicone of a graded direct sum. -/
def degreeZeroLift (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q)
    (s : BinaryFan (⟨x⟩ : DegreeZero (R := R) C ι)
      (⟨y⟩ : DegreeZero (R := R) C ι)) :
    s.pt ⟶ (⟨z⟩ : DegreeZero (R := R) C ι) :=
  ⟨(s.fst.hom ≫ i : s.pt.obj ⟶ z) + (s.snd.hom ≫ j : s.pt.obj ⟶ z),
    Submodule.add_mem _
      (GradedCategory.comp_mem_homDegree_zero (ι := ι) s.fst.property
        hds.i_mem_homDegree_zero)
      (GradedCategory.comp_mem_homDegree_zero (ι := ι) s.snd.property
        hds.j_mem_homDegree_zero)⟩

/-- The coproduct comparison map out of the degree-zero bicone of a graded direct sum. -/
def degreeZeroDesc (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q)
    (s : BinaryCofan (⟨x⟩ : DegreeZero (R := R) C ι)
      (⟨y⟩ : DegreeZero (R := R) C ι)) :
    (⟨z⟩ : DegreeZero (R := R) C ι) ⟶ s.pt :=
  ⟨(p ≫ s.inl.hom : z ⟶ s.pt.obj) + (q ≫ s.inr.hom : z ⟶ s.pt.obj),
    Submodule.add_mem _
      (GradedCategory.comp_mem_homDegree_zero (ι := ι) hds.p_mem_homDegree_zero
        s.inl.property)
      (GradedCategory.comp_mem_homDegree_zero (ι := ι) hds.q_mem_homDegree_zero
        s.inr.property)⟩

/-- The degree-zero bicone of a graded direct sum is a binary bilimit. -/
def degreeZeroIsBilimit (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    (degreeZeroBicone hds).IsBilimit where
  isLimit :=
    { lift := fun s => degreeZeroLift hds s
      fac := sorry
      uniq := sorry }
  isColimit :=
    { desc := fun s => degreeZeroDesc hds s
      fac := sorry
      uniq := sorry }

/-- The degree-zero bicone of a graded direct sum is a limit cone. -/
def degreeZeroIsLimit (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    IsLimit (degreeZeroBicone hds).toCone :=
  (degreeZeroIsBilimit hds).isLimit

/-- The degree-zero bicone of a graded direct sum is a colimit cocone. -/
def degreeZeroIsColimit (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    IsColimit (degreeZeroBicone hds).toCocone :=
  (degreeZeroIsBilimit hds).isColimit

/-- A graded direct sum supplies a binary biproduct in the degree-zero category. -/
abbrev hasBinaryBiproductDegreeZero
    (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    HasBinaryBiproduct (⟨x⟩ : DegreeZero (R := R) C ι)
      (⟨y⟩ : DegreeZero (R := R) C ι) :=
  HasBinaryBiproduct.mk
    { bicone := degreeZeroBicone hds
      isBilimit := degreeZeroIsBilimit hds }

/-- The ambient binary bicone determined by graded direct-sum data. -/
def bicone (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) : BinaryBicone x y where
  pt := z
  fst := p
  snd := q
  inl := i
  inr := j
  inl_fst := hds.i_comp_p
  inl_snd := hds.i_comp_q
  inr_fst := hds.j_comp_p
  inr_snd := hds.j_comp_q

/-- The first projection of the ambient bicone is the supplied projection. -/
@[simp]
theorem bicone_fst (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    (bicone hds).fst = p := sorry

/-- The second projection of the ambient bicone is the supplied projection. -/
@[simp]
theorem bicone_snd (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    (bicone hds).snd = q := sorry

/-- The first injection of the ambient bicone is the supplied injection. -/
@[simp]
theorem bicone_inl (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    (bicone hds).inl = i := sorry

/-- The second injection of the ambient bicone is the supplied injection. -/
@[simp]
theorem bicone_inr (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    (bicone hds).inr = j := sorry

/-- The ambient bicone of a graded direct sum satisfies the binary-biproduct total identity. -/
theorem bicone_total (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    (bicone hds).fst ≫ (bicone hds).inl + (bicone hds).snd ≫ (bicone hds).inr =
      𝟙 (bicone hds).pt := sorry

/-- The ambient bicone of a graded direct sum is a binary bilimit. -/
def isBilimit (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    (bicone hds).IsBilimit :=
  isBinaryBilimitOfTotal (bicone hds) (bicone_total hds)

/-- The ambient bicone of a graded direct sum is a limit cone. -/
def isLimit (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    IsLimit (bicone hds).toCone :=
  (isBilimit hds).isLimit

/-- The ambient bicone of a graded direct sum is a colimit cocone. -/
def isColimit (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) :
    IsColimit (bicone hds).toCocone :=
  (isBilimit hds).isColimit

/-- A graded direct sum supplies a binary biproduct in the ambient category. -/
abbrev hasBinaryBiproduct
    (hds : IsGradedDirectSum (R := R) (ι := ι) i j p q) : HasBinaryBiproduct x y :=
  HasBinaryBiproduct.mk
    { bicone := bicone hds
      isBilimit := isBilimit hds }

end IsGradedDirectSum

end

end GradedCategory

end CategoryTheory
