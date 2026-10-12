/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Total
public import ReasLib.CategoryTheory.Monoidal.FunctorCategory
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Monoidal
public import ReasLib.CategoryTheory.GradedObject.Monoidal.MapObj
public import ReasLib.Algebra.Homology.Embedding.UpNatMonoidal
public import ReasLib.AlgebraicTopology.CosimplicialObject.Tensor.AlexanderWhitney
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Tensor comparisons of total Cech complexes

This leaf owns the coefficient-independent data-to-map boundary for the Cech tensor comparison
and the canonical front/back Alexander--Whitney map on each Cech row.  It does not identify a
Cartesian product with a tensor product.  Assembling the row maps across the two outer complex
degrees requires a separate four-degree totalization comparison; a universe-polymorphic
`ModuleCat` specialization is additionally needed to interpret the coefficient tensor as
`⊗_ℤ` for arbitrary cover universes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape HomologicalComplex
open CategoryTheory.MonoidalCategory

noncomputable section

universe w vA uA v u

namespace CategoryTheory.Cech.Tensor

open CategoryTheory.Cech.Total

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
variable [HasZeroObject A] [HasCoproducts A]
variable [MonoidalCategory A] [MonoidalPreadditive A]
variable {ι : Type w}
variable (U : ι → C) (F G : CochainComplex (Cᵒᵖ ⥤ A) ℤ)

/-- The source total tensor complex in the Cech comparison. -/
@[stacks 07MB "source total tensor complex for the Cech comparison"]
abbrev source :=
  HomologicalComplex.tensorObj ((totalCechFunctor U).obj F) ((totalCechFunctor U).obj G)

/-- The target total Cech complex of the tensor product of the coefficient complexes. -/
@[stacks 07MB "target total Cech complex for the tensor comparison"]
abbrev target :=
  (totalCechFunctor U).obj (HomologicalComplex.tensorObj F G)

/-- Descend a family of homogeneous tensor components into one total degree. -/
@[stacks 07MB "homogeneous component descent for the Cech tensor comparison"]
abbrev componentMap (n : ℤ) {M : A}
    (f : ∀ p q (_ : p + q = n),
      ((totalCechFunctor U).obj F).X p ⊗ ((totalCechFunctor U).obj G).X q ⟶ M) :
    (source U F G).X n ⟶ M :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := (totalCechFunctor U).obj F) (K₂ := (totalCechFunctor U).obj G)
    (F := MonoidalCategory.curriedTensor A) (c := up ℤ) f

/-- Explicit homogeneous data for a Cech tensor comparison.

The component family records the actual coefficient-category tensor maps; the relation field records
their compatibility with the total differentials.  Both are explicit inputs, so this structure does
not hide a chosen map or a product-to-tensor comparison behind an existential witness.
-/
structure Components where
  /-- The map from each homogeneous tensor summand to the target total degree. -/
  component : ∀ p q n (_ : p + q = n),
    ((totalCechFunctor U).obj F).X p ⊗ ((totalCechFunctor U).obj G).X q ⟶ (target U F G).X n
  /-- Compatibility of the homogeneous components with the cochain differentials. -/
  comm : ∀ i j, (up ℤ).Rel i j →
    componentMap U F G i (fun p q h ↦ component p q i h) ≫ (target U F G).d i j =
      (source U F G).d i j ≫ componentMap U F G j (fun p q h ↦ component p q j h)

/-- Assemble homogeneous Cech tensor components into a cochain morphism. -/
@[stacks 07MB "Cech tensor comparison from explicit homogeneous data"]
noncomputable def Components.hom (D : Components U F G) : source U F G ⟶ target U F G :=
  HomologicalComplex.Hom.mk
    (fun n ↦ componentMap U F G n (fun p q h ↦ D.component p q n h)) D.comm

/-- The degree-`n` component of `Components.hom` is the corresponding homogeneous descent. -/
@[simp, stacks 07MB "degree component of the Cech tensor comparison"]
theorem Components.hom_f (D : Components U F G) (n : ℤ) :
    D.hom.f n = componentMap U F G n (fun p q h ↦ D.component p q n h) := sorry

section Row

variable {C : Type u} [Category.{v} C]
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [MonoidalCategory A]
  [MonoidalPreadditive A] [HasProducts.{w} A] [HasZeroObject A] [HasCoproducts A]

/-- The pointwise tensor map induced by a simplicial formal-coproduct object. -/
@[stacks 07MB "formal-coproduct cosimplicial tensor comparison"]
noncomputable def cosimplicialTensorHom
    (E : SimplicialObject (FormalCoproduct.{w} C)) (F G : Cᵒᵖ ⥤ A) :
    (FormalCoproduct.cosimplicialObjectFunctor (C := C) (A := A) E).obj F ⊗
        (FormalCoproduct.cosimplicialObjectFunctor (C := C) (A := A) E).obj G ⟶
      (FormalCoproduct.cosimplicialObjectFunctor (C := C) (A := A) E).obj (F ⊗ G) :=
  let H :=
    (Functor.whiskeringLeft SimplexCategory (FormalCoproduct.{w} C)ᵒᵖ A).obj E.rightOp
  Functor.LaxMonoidal.μ H ((FormalCoproduct.evalOp C A).obj F)
      ((FormalCoproduct.evalOp C A).obj G) ≫
    H.map (FormalCoproduct.evalOpTensorHom F G)

/-- The cosimplicial tensor map is natural in both coefficient presheaves. -/
@[reassoc, stacks 07MB "coefficient naturality of the cosimplicial tensor map"]
theorem cosimplicialTensorHom_naturality
    (E : SimplicialObject (FormalCoproduct.{w} C))
    {F F' G G' : Cᵒᵖ ⥤ A} (f : F ⟶ F') (g : G ⟶ G') :
    (((FormalCoproduct.cosimplicialObjectFunctor E).map f) ⊗ₘ
        ((FormalCoproduct.cosimplicialObjectFunctor E).map g)) ≫
      cosimplicialTensorHom E F' G' =
    cosimplicialTensorHom E F G ≫
      (FormalCoproduct.cosimplicialObjectFunctor E).map (f ⊗ₘ g) := sorry

/-- The alternating-Cech row tensor comparison. -/
@[stacks 07MB "alternating Cech row tensor comparison"]
noncomputable def rowComparison
    (E : SimplicialObject (FormalCoproduct.{w} C)) (F G : Cᵒᵖ ⥤ A) :
    HomologicalComplex.tensorObj
        ((FormalCoproduct.cochainComplexFunctor (C := C) (A := A) E).obj F)
        ((FormalCoproduct.cochainComplexFunctor (C := C) (A := A) E).obj G) ⟶
      ((FormalCoproduct.cochainComplexFunctor (C := C) (A := A) E).obj (F ⊗ G)) :=
  AlgebraicTopology.alternatingCofaceMapComplex.tensorComparison
      ((FormalCoproduct.cosimplicialObjectFunctor (C := C) (A := A) E).obj F)
      ((FormalCoproduct.cosimplicialObjectFunctor (C := C) (A := A) E).obj G) ≫
    (AlgebraicTopology.alternatingCofaceMapComplex A).map
      (cosimplicialTensorHom E F G)

/-- The row tensor comparison is natural in both presheaves. -/
@[stacks 07MB "naturality of the Cech row tensor comparison"]
theorem rowComparison_naturality
    (E : SimplicialObject (FormalCoproduct.{w} C))
    {F F' G G' : Cᵒᵖ ⥤ A} (f : F ⟶ F') (g : G ⟶ G') :
    HomologicalComplex.tensorHom
        ((FormalCoproduct.cochainComplexFunctor E).map f)
        ((FormalCoproduct.cochainComplexFunctor E).map g) ≫
      rowComparison E F' G' =
    rowComparison E F G ≫
      (FormalCoproduct.cochainComplexFunctor E).map (f ⊗ₘ g) := sorry

section Cech

variable [HasFiniteProducts C] {ι : Type w}

/-- The row tensor comparison for an indexed Cech family. -/
@[stacks 07MB "Cech family row tensor comparison"]
noncomputable def cechRowComparison (U : ι → C) (F G : Cᵒᵖ ⥤ A) :
    HomologicalComplex.tensorObj
        ((cechComplexFunctor U).obj F)
        ((cechComplexFunctor U).obj G) ⟶
      (cechComplexFunctor U).obj (F ⊗ G) :=
  rowComparison (FormalCoproduct.mk _ U).cech F G

/-- The family-level row tensor comparison is natural in both presheaves. -/
@[stacks 07MB "naturality of the Cech-family row tensor comparison"]
theorem cechRowComparison_naturality
    (U : ι → C) {F F' G G' : Cᵒᵖ ⥤ A} (f : F ⟶ F') (g : G ⟶ G') :
    HomologicalComplex.tensorHom
        ((cechComplexFunctor U).map f)
        ((cechComplexFunctor U).map g) ≫
      cechRowComparison U F' G' =
    cechRowComparison U F G ≫
      (cechComplexFunctor U).map (f ⊗ₘ g) := sorry

end Cech

end Row

section TotalComparison

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
variable [HasZeroObject A] [HasCoproducts A]
variable [MonoidalCategory A] [MonoidalPreadditive A]
variable {ι : Type w}
variable [∀ Z : A, PreservesColimitsOfSize.{0, 0} ((curriedTensor A).obj Z)]
variable [∀ Z : A, PreservesColimitsOfSize.{0, 0} ((curriedTensor A).flip.obj Z)]

/-- Extend a natural-degree Cech row comparison to the integer-indexed row complexes. -/
@[stacks 07MB "integer-indexed Cech row tensor comparison"]
noncomputable def rowComparisonZ (U : ι → C) (F G : Cᵒᵖ ⥤ A) :
    HomologicalComplex.tensorObj ((rowCechFunctor U).obj F) ((rowCechFunctor U).obj G) ⟶
      (rowCechFunctor U).obj (F ⊗ G) :=
  (embeddingUpNat.extendTensorIso ((cechComplexFunctor U).obj F)
      ((cechComplexFunctor U).obj G)).hom ≫
    (embeddingUpNat.extendFunctor A).map (cechRowComparison U F G)

/-- Reassociate the two inner total degrees after the outer tensor degree is fixed. -/
@[stacks 07MB "degree rearrangement for the Cech tensor comparison"]
theorem interchangedDegree {p q n : ℤ} (hpq : p + q = n) {x y : ℤ × ℤ}
    (hx : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) x = p)
    (hy : ComplexShape.π (up ℤ) (up ℤ) (up ℤ) y = q) :
    ComplexShape.π (up ℤ) (up ℤ) (up ℤ) (x.1 + y.1, x.2 + y.2) = n := sorry

/-- The canonical homogeneous four-degree component of the Cech tensor comparison. -/
@[stacks 07MB "homogeneous four-degree Cech tensor comparison"]
noncomputable def comparisonComponent (U : ι → C)
    (F G : CochainComplex (Cᵒᵖ ⥤ A) ℤ) (n : ℤ) {a b : ℤ} (h : a + b = n) :
    ((totalCechFunctor U).obj F).X a ⊗ ((totalCechFunctor U).obj G).X b ⟶
      (target U F G).X n :=
  GradedObject.mapObjTensorDesc
    ((doubleCechFunctor U).obj F).toGradedObject
    ((doubleCechFunctor U).obj G).toGradedObject
    (ComplexShape.π (up ℤ) (up ℤ) (up ℤ))
    (ComplexShape.π (up ℤ) (up ℤ) (up ℤ)) a b
    (fun x hx y hy ↦
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) x.2 y.1) •
        (HomologicalComplex.ιTensorObj
          ((rowCechFunctor U).obj (F.X x.1))
          ((rowCechFunctor U).obj (G.X y.1)) x.2 y.2 (x.2 + y.2) rfl ≫
        (rowComparisonZ U (F.X x.1) (G.X y.1)).f (x.2 + y.2) ≫
        ((rowCechFunctor U).map
          (HomologicalComplex.ιTensorObj F G x.1 y.1 (x.1 + y.1) rfl)).f (x.2 + y.2) ≫
        (((doubleCechFunctor U).obj (HomologicalComplex.tensorObj F G)).ιTotal
          (up ℤ) (x.1 + y.1) (x.2 + y.2) n
          (interchangedDegree h hx hy))))

/-- The canonical homogeneous components commute with the total differentials. -/
@[stacks 07MB "chain compatibility of the Cech tensor components"]
theorem comparisonComponent_comm (U : ι → C)
    (F G : CochainComplex (Cᵒᵖ ⥤ A) ℤ) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    componentMap U F G i (fun p q h ↦ comparisonComponent U F G i h) ≫
        (target U F G).d i j =
      (source U F G).d i j ≫
        componentMap U F G j (fun p q h ↦ comparisonComponent U F G j h) := sorry

/-- Bundle the canonical Cech tensor components and their chain compatibility law. -/
@[stacks 07MB "canonical Cech tensor comparison components"]
noncomputable def components (U : ι → C)
    (F G : CochainComplex (Cᵒᵖ ⥤ A) ℤ) : Components U F G :=
  { component := fun p q n h ↦ comparisonComponent U F G n h
    comm := comparisonComponent_comm U F G }

/-- 20.25.3.2 (07MB): the canonical tensor comparison of total Cech complexes. -/
@[stacks 07MB "canonical tensor comparison of total Cech complexes"]
noncomputable def comparison (U : ι → C)
    (F G : CochainComplex (Cᵒᵖ ⥤ A) ℤ) : source U F G ⟶ target U F G :=
  (components U F G).hom

/-- The degree component of the canonical total Cech tensor comparison. -/
@[simp, stacks 07MB "degree component of the canonical total Cech comparison"]
theorem comparison_f (U : ι → C) (F G : CochainComplex (Cᵒᵖ ⥤ A) ℤ) (n : ℤ) :
    (comparison U F G).f n =
      componentMap U F G n (fun p q h ↦ comparisonComponent U F G n h) := sorry

end TotalComparison

end CategoryTheory.Cech.Tensor

end
