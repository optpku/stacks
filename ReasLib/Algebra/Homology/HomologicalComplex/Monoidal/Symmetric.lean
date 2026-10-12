/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.GradedObject.Braiding
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Koszul symmetry on homological complexes

@stack 0FP8

The Koszul braiding depends only on a commutative grading monoid and the tensor signs of the
complex shape.  This file owns that general construction; chain and cochain complexes merely
install the corresponding instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace ComplexShape

variable {I : Type*} [AddCommMonoid I] (c : ComplexShape I)
variable [c.TensorSigns] [TotalComplexShapeSymmetry c c c]

/-- A total-complex interchange sign is a braiding sign when it is additive in each degree.
These are exactly the extra sign laws used by the two braided hexagons. -/
@[stacks 0FP8 "braiding signs for homological complexes"]
class BraidingSigns : Prop where
  /-- The interchange sign is multiplicative in the left degree. -/
  sigma_add_left (p q r : I) : σ c c c (p + q) r = σ c c c p r * σ c c c q r
  /-- The interchange sign is multiplicative in the right degree. -/
  sigma_add_right (p q r : I) : σ c c c p (q + r) = σ c c c p q * σ c c c p r

end ComplexShape

namespace HomologicalComplex.Koszul

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Limits.HasZeroObject C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
variable {I : Type*} (c : ComplexShape I)

/-- The flipped pointwise tensor bicomplex before totalization. -/
abbrev pointwiseSource (K L : HomologicalComplex C c) :=
  (((curriedTensor C).flip.mapBifunctorHomologicalComplex c c).obj L).obj K

/-- The ordinary pointwise tensor bicomplex before totalization. -/
abbrev pointwiseTarget (K L : HomologicalComplex C c) :=
  (((curriedTensor C).mapBifunctorHomologicalComplex c c).obj L).obj K

/-- The base-category braiding on one entry of the pointwise tensor bicomplex. -/
abbrev pointwiseComponent (K L : HomologicalComplex C c) (q p : I) :
    (pointwiseSource c K L).toGradedObject ⟨q, p⟩ ⟶
      (pointwiseTarget c K L).toGradedObject ⟨q, p⟩ :=
  (((BraidedCategory.curriedBraidingNatIso C).app (K.X p)).app (L.X q)).hom

/-- Pointwise braiding commutes with the inner differential. -/
theorem pointwiseComponent_natural_inner
    (K L : HomologicalComplex C c) (q p p' : I) (hp : c.Rel p p') :
    pointwiseComponent c K L q p ≫ ((pointwiseTarget c K L).X q).d p p' =
      ((pointwiseSource c K L).X q).d p p' ≫
        pointwiseComponent c K L q p' := sorry

/-- The pointwise braiding is an isomorphism in each outer degree. -/
def pointwiseColumnIso (K L : HomologicalComplex C c) (q : I) :
    (pointwiseSource c K L).X q ≅ (pointwiseTarget c K L).X q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ ((BraidedCategory.curriedBraidingNatIso C).app (K.X p)).app (L.X q))
    (pointwiseComponent_natural_inner c K L q)

/-- Pointwise braiding commutes with the outer differential. -/
theorem pointwiseColumnIso_natural_outer
    (K L : HomologicalComplex C c) (q q' : I) (hq : c.Rel q q') :
    (pointwiseColumnIso c K L q).hom ≫ (pointwiseTarget c K L).d q q' =
      (pointwiseSource c K L).d q q' ≫ (pointwiseColumnIso c K L q').hom := sorry

/-- The flipped and ordinary pointwise tensor bicomplexes are canonically isomorphic. -/
def pointwiseIso (K L : HomologicalComplex C c) :
    pointwiseSource c K L ≅ pointwiseTarget c K L :=
  HomologicalComplex.Hom.isoOfComponents
    (pointwiseColumnIso c K L) (pointwiseColumnIso_natural_outer c K L)

/-- Swapping two homogeneous degrees preserves their total degree. -/
theorem swap_degree_eq [AddCommMonoid I] {p q n : I} (h : p + q = n) : q + p = n := sorry

variable [AddCommMonoid I] [DecidableEq I]
variable [c.TensorSigns] [TotalComplexShapeSymmetry c c c]
variable [∀ G₁ G₂ : GradedObject I C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject I C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject I C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject I C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]

/-- The Koszul braiding: flip totalization directions, then braid the tensor factors pointwise. -/
@[stacks 0FP8 "Koszul braiding on homological complexes"]
def braiding (K L : HomologicalComplex C c) : K ⊗ L ≅ L ⊗ K :=
  (HomologicalComplex.mapBifunctorFlipIso K L (curriedTensor C) c).symm ≪≫
    HomologicalComplex₂.total.mapIso (pointwiseIso c K L) c

/-- On a homogeneous summand, the braiding is the base braiding multiplied by the tensor sign. -/
@[reassoc]
theorem ι_braiding_hom
    (K L : HomologicalComplex C c) (p q n : I) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ (braiding c K L).hom.f n =
      (ComplexShape.σ c c c p q • (β_ (K.X p) (L.X q)).hom) ≫
        HomologicalComplex.ιTensorObj L K q p n (swap_degree_eq h) := sorry

/-- The Koszul braiding is natural in its right argument. -/
theorem braiding_natural_right
    (K : HomologicalComplex C c) {L M : HomologicalComplex C c} (f : L ⟶ M) :
    K ◁ f ≫ (braiding c K M).hom = (braiding c K L).hom ≫ f ▷ K := sorry

/-- The Koszul braiding is natural in its left argument. -/
theorem braiding_natural_left
    {K L : HomologicalComplex C c} (f : K ⟶ L) (M : HomologicalComplex C c) :
    f ▷ M ≫ (braiding c L M).hom = (braiding c K M).hom ≫ M ◁ f := sorry

/-- The Koszul braiding satisfies the forward hexagon identity. -/
theorem braiding_hexagon_forward
    [ComplexShape.BraidingSigns c]
    (K L M : HomologicalComplex C c) :
    (α_ K L M).hom ≫ (braiding c K (L ⊗ M)).hom ≫ (α_ L M K).hom =
      (braiding c K L).hom ▷ M ≫ (α_ L K M).hom ≫
        L ◁ (braiding c K M).hom := sorry

/-- The Koszul braiding satisfies the reverse hexagon identity. -/
theorem braiding_hexagon_reverse
    [ComplexShape.BraidingSigns c]
    (K L M : HomologicalComplex C c) :
    (α_ K L M).inv ≫ (braiding c (K ⊗ L) M).hom ≫ (α_ M K L).inv =
      K ◁ (braiding c L M).hom ≫ (α_ K M L).inv ≫
        (braiding c K M).hom ▷ L := sorry

/-- Applying the Koszul braiding twice is the identity. -/
theorem braiding_symmetry [TotalComplexShapeSymmetrySymmetry c c c]
    (K L : HomologicalComplex C c) :
    (braiding c K L).hom ≫ (braiding c L K).hom = 𝟙 (K ⊗ L) := sorry

/-- The braided monoidal structure induced by the Koszul braiding. -/
@[stacks 0FP8 "homological-complex braided structure", implicit_reducible]
noncomputable def braidedCategory [ComplexShape.BraidingSigns c] :
    BraidedCategory (HomologicalComplex C c) where
  braiding := braiding c
  braiding_naturality_right := braiding_natural_right c
  braiding_naturality_left := braiding_natural_left c
  hexagon_forward := braiding_hexagon_forward c
  hexagon_reverse := braiding_hexagon_reverse c

/-- The symmetric monoidal structure induced by the Koszul braiding. -/
@[stacks 0FP8 "homological-complex symmetric structure", implicit_reducible]
noncomputable def symmetricCategory [ComplexShape.BraidingSigns c]
    [TotalComplexShapeSymmetrySymmetry c c c] :
    SymmetricCategory (HomologicalComplex C c) where
  toBraidedCategory := braidedCategory c
  symmetry := braiding_symmetry c

end HomologicalComplex.Koszul

