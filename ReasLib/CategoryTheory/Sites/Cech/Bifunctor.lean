module

public import ReasLib.CategoryTheory.Sites.Cech.Total
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Bifunctor
public import ReasLib.Algebra.Homology.Embedding.Bifunctor
public import ReasLib.Algebra.Homology.Embedding.UpNatMonoidal
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Monoidal
public import ReasLib.AlgebraicTopology.SimplexCategory.FrontBack
public import ReasLib.Algebra.Homology.ComplexShapeSigns.Nat
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Heterogeneous Cech row comparisons

This leaf keeps the coefficient bifunctor explicit.  In particular, the two input coefficient
categories may have different universes, so a module specialization can use
`ModuleCat.TensorProduct.functor` instead of a same-universe monoidal structure.  The row map is
concrete; only its naturality and chain-compatibility laws are deferred at the statement stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape HomologicalComplex
open Opposite
open scoped Simplicial

noncomputable section

universe w uA vA uB vB uD vD v u

namespace CategoryTheory.Cech.Bifunctor

variable {C : Type u} [Category.{v} C]
variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {D : Type uD} [Category.{vD} D]
variable {T : A ⥤ B ⥤ D}
variable {F : Cᵒᵖ ⥤ A} {G : Cᵒᵖ ⥤ B}

/-! ### Pointwise coefficient bifunctors -/

/-- The curried bifunctor obtained by applying a coefficient bifunctor pointwise to presheaves. -/
@[stacks 07MB "pointwise coefficient bifunctor on presheaf categories"]
abbrev pointwiseFunctor (T : A ⥤ B ⥤ D) :
    (Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ B) ⥤ Cᵒᵖ ⥤ D :=
  Functor.PointwiseBifunctor.functor T

/-- The pointwise object of a curried coefficient bifunctor. -/
@[stacks 07MB "pointwise coefficient bifunctor on presheaves"]
abbrev pointwiseObj (T : A ⥤ B ⥤ D) (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B) : Cᵒᵖ ⥤ D :=
  ((pointwiseFunctor T).obj F).obj G

/-- The pointwise presheaf morphism induced by morphisms in both coefficient variables. -/
@[stacks 07MB "pointwise coefficient bifunctor map on presheaves"]
abbrev pointwiseMap (T : A ⥤ B ⥤ D) {F F' : Cᵒᵖ ⥤ A} {G G' : Cᵒᵖ ⥤ B}
    (f : F ⟶ F') (g : G ⟶ G') : pointwiseObj T F G ⟶ pointwiseObj T F' G' :=
  Functor.PointwiseBifunctor.map T f g

section Cosimplicial

variable [HasProducts.{w} A] [HasProducts.{w} B] [HasProducts.{w} D]

/-- The induced natural transformation on a cosimplicial object. -/
@[stacks 07MB "cosimplicial heterogeneous Cech bifunctor map"]
noncomputable def cosimplicialBifunctorHom
    (E : SimplicialObject (FormalCoproduct.{w} C))
    (T : A ⥤ B ⥤ D) (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B) :
    (((Functor.whiskeringRight₂ SimplexCategory A B D).obj T).obj
      ((FormalCoproduct.cosimplicialObjectFunctor (C := C) (A := A) E).obj F)).obj
      ((FormalCoproduct.cosimplicialObjectFunctor (C := C) (A := B) E).obj G) ⟶
      (FormalCoproduct.cosimplicialObjectFunctor (C := C) (A := D) E).obj (pointwiseObj T F G) :=
  let H := (Functor.whiskeringLeft SimplexCategory (FormalCoproduct.{w} C)ᵒᵖ D).obj E.rightOp
  H.map (FormalCoproduct.Bifunctor.hom T F G)

end Cosimplicial

section Row

variable (E : SimplicialObject (FormalCoproduct.{w} C))
variable [Preadditive A] [HasProducts.{w} A]
variable [Preadditive B] [HasProducts.{w} B]
variable [Preadditive D] [HasProducts.{w} D] [HasCoproducts D]

/-- The degree equation supplied by the natural Cech shape relation. -/
@[stacks 07MB "natural Cech degree relation"]
theorem degreeEq {p q n : ℕ}
    (h : (up ℕ).π (up ℕ) (up ℕ) (p, q) = n) : p + q = n := sorry

/-- The front/back coefficient component in natural Cech degree. -/
@[stacks 07MB "front-back component of a heterogeneous Cech row map"]
noncomputable def rowComponent (T : A ⥤ B ⥤ D)
    (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B) (n : ℕ)
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms] :
    (HomologicalComplex.mapBifunctor
      ((FormalCoproduct.cochainComplexFunctor (C := C) (A := A) E).obj F)
      ((FormalCoproduct.cochainComplexFunctor (C := C) (A := B) E).obj G)
      T (up ℕ)).X n ⟶
    ((FormalCoproduct.cochainComplexFunctor (C := C) (A := D) E).obj
      (pointwiseObj T F G)).X n :=
  let X := (FormalCoproduct.cosimplicialObjectFunctor (C := C) (A := A) E).obj F
  let Y := (FormalCoproduct.cosimplicialObjectFunctor (C := C) (A := B) E).obj G
  HomologicalComplex.mapBifunctorDesc
    (K₁ := (FormalCoproduct.cochainComplexFunctor (C := C) (A := A) E).obj F)
    (K₂ := (FormalCoproduct.cochainComplexFunctor (C := C) (A := B) E).obj G)
    (F := T) (c := up ℕ)
    (fun p q h ↦
      (T.map (X.map (SimplexCategory.frontOfAddEq p q n (degreeEq h)))).app
          (Y.obj ⦋q⦌) ≫
        (T.obj (X.obj ⦋n⦌)).map
          (Y.map (SimplexCategory.backOfAddEq p q n (degreeEq h))) ≫
        (cosimplicialBifunctorHom E T F G).app ⦋n⦌)

/-- The front/back components commute with the alternating Cech differential. -/
@[stacks 07MB "chain compatibility of a heterogeneous Cech row map"]
theorem rowComponent_comm (T : A ⥤ B ⥤ D)
    (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B)
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
    (i j : ℕ) (hij : (up ℕ).Rel i j) :
    rowComponent E T F G i ≫
        ((FormalCoproduct.cochainComplexFunctor (C := C) (A := D) E).obj
          (pointwiseObj T F G)).d i j =
      (HomologicalComplex.mapBifunctor
          ((FormalCoproduct.cochainComplexFunctor (C := C) (A := A) E).obj F)
          ((FormalCoproduct.cochainComplexFunctor (C := C) (A := B) E).obj G)
          T (up ℕ)).d i j ≫ rowComponent E T F G j := sorry

/-- The resulting heterogeneous map of alternating Cech row complexes. -/
@[stacks 07MB "heterogeneous alternating Cech row comparison"]
noncomputable def rowComparison (T : A ⥤ B ⥤ D)
    (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B)
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms] :
    HomologicalComplex.mapBifunctor
        ((FormalCoproduct.cochainComplexFunctor (C := C) (A := A) E).obj F)
        ((FormalCoproduct.cochainComplexFunctor (C := C) (A := B) E).obj G)
        T (up ℕ) ⟶
      ((FormalCoproduct.cochainComplexFunctor (C := C) (A := D) E).obj
        (pointwiseObj T F G)) :=
  HomologicalComplex.Hom.mk (fun n ↦ rowComponent E T F G n)
    (rowComponent_comm E T F G)

@[simp, stacks 07MB "degree component of a heterogeneous Cech row comparison"]
theorem rowComparison_f (T : A ⥤ B ⥤ D)
    (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B)
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
    (n : ℕ) :
    (rowComparison E T F G).f n = rowComponent E T F G n := sorry

/-- The heterogeneous row comparison is natural in both coefficient presheaves. -/
@[stacks 07MB "naturality of the heterogeneous Cech row comparison"]
theorem rowComparison_naturality (T : A ⥤ B ⥤ D)
    {F F' : Cᵒᵖ ⥤ A} {G G' : Cᵒᵖ ⥤ B}
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
    (f : F ⟶ F') (g : G ⟶ G') :
    HomologicalComplex.mapBifunctorMap
        ((FormalCoproduct.cochainComplexFunctor (C := C) (A := A) E).map f)
        ((FormalCoproduct.cochainComplexFunctor (C := C) (A := B) E).map g)
        T (up ℕ) ≫ rowComparison E T F' G' =
      rowComparison E T F G ≫
        (FormalCoproduct.cochainComplexFunctor (C := C) (A := D) E).map
          (pointwiseMap T f g) := sorry

end Row

section Family

variable [HasFiniteProducts C] {ι : Type w}
variable [Preadditive A] [HasProducts.{w} A]
variable [Preadditive B] [HasProducts.{w} B]
variable [Preadditive D] [HasProducts.{w} D] [HasCoproducts D]

/-- The heterogeneous row comparison for an indexed Cech family. -/
@[stacks 07MB "heterogeneous Cech-family row comparison"]
noncomputable def cechRowComparison (T : A ⥤ B ⥤ D) (U : ι → C)
    (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B)
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms] :
    HomologicalComplex.mapBifunctor ((cechComplexFunctor U).obj F)
        ((cechComplexFunctor U).obj G) T (up ℕ) ⟶
      (cechComplexFunctor U).obj (pointwiseObj T F G) :=
  rowComparison (FormalCoproduct.mk _ U).cech T F G

/-- The degree component of the heterogeneous family-level row comparison. -/
@[stacks 07MB "degree component of the heterogeneous Cech-family row comparison"]
theorem cechRowComparison_f (T : A ⥤ B ⥤ D) (U : ι → C)
    (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B)
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
    (n : ℕ) :
    (cechRowComparison T U F G).f n =
      rowComponent (FormalCoproduct.mk _ U).cech T F G n := sorry

/-- The heterogeneous family-level row comparison is natural in both coefficient presheaves. -/
@[stacks 07MB "naturality of the heterogeneous Cech-family row comparison"]
theorem cechRowComparison_naturality (T : A ⥤ B ⥤ D) (U : ι → C)
    {F F' : Cᵒᵖ ⥤ A} {G G' : Cᵒᵖ ⥤ B}
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
    (f : F ⟶ F') (g : G ⟶ G') :
    HomologicalComplex.mapBifunctorMap ((cechComplexFunctor U).map f)
        ((cechComplexFunctor U).map g) T (up ℕ) ≫ cechRowComparison T U F' G' =
      cechRowComparison T U F G ≫
        (cechComplexFunctor U).map (pointwiseMap T f g) := sorry

end Family

section IntegerRow

open Total

variable [HasFiniteProducts C] {ι : Type w}
variable [Preadditive A] [HasZeroObject A] [HasProducts.{w} A]
variable [Preadditive B] [HasZeroObject B] [HasProducts.{w} B]
variable [Preadditive D] [HasZeroObject D] [HasProducts.{w} D] [HasCoproducts D]

/-- Extend the heterogeneous Cech row comparison from natural cochain degrees to integer
cochain degrees. -/
@[stacks 07MB "integer-indexed heterogeneous Cech row comparison"]
noncomputable def rowComparisonZ (T : A ⥤ B ⥤ D) (U : ι → C)
    (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B)
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms] :
    HomologicalComplex.mapBifunctor ((rowCechFunctor (A := A) U).obj F)
        ((rowCechFunctor (A := B) U).obj G) T (up ℤ) ⟶
      (rowCechFunctor (A := D) U).obj (pointwiseObj T F G) :=
  ComplexShape.embeddingUpNat.extendBifunctorHom T
      ((cechComplexFunctor U).obj F) ((cechComplexFunctor U).obj G) ≫
    (ComplexShape.embeddingUpNat.extendFunctor D).map
      (rowComparison (FormalCoproduct.mk _ U).cech T F G)

/-- The degree component of the integer-indexed heterogeneous Cech row comparison is the
extension comparison followed by the extended natural-degree row map. -/
@[stacks 07MB "degree component of the integer-indexed heterogeneous Cech row comparison"]
theorem rowComparisonZ_f (T : A ⥤ B ⥤ D) (U : ι → C)
    (F : Cᵒᵖ ⥤ A) (G : Cᵒᵖ ⥤ B)
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms] (n : ℤ) :
    (rowComparisonZ T U F G).f n =
      (ComplexShape.embeddingUpNat.extendBifunctorHom T
          ((cechComplexFunctor U).obj F) ((cechComplexFunctor U).obj G)).f n ≫
        ((ComplexShape.embeddingUpNat.extendFunctor D).map
          (rowComparison (FormalCoproduct.mk _ U).cech T F G)).f n := sorry

/-- The integer-indexed heterogeneous row comparison is natural in both coefficient
presheaves. -/
@[stacks 07MB "naturality of the integer-indexed heterogeneous Cech row comparison"]
theorem rowComparisonZ_naturality (T : A ⥤ B ⥤ D) (U : ι → C)
    {F F' : Cᵒᵖ ⥤ A} {G G' : Cᵒᵖ ⥤ B}
    [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
    (f : F ⟶ F') (g : G ⟶ G') :
    HomologicalComplex.mapBifunctorMap
        ((rowCechFunctor (A := A) U).map f) ((rowCechFunctor (A := B) U).map g)
        T (up ℤ) ≫ rowComparisonZ T U F' G' =
      rowComparisonZ T U F G ≫
        (rowCechFunctor (A := D) U).map (pointwiseMap T f g) := sorry

end IntegerRow

end CategoryTheory.Cech.Bifunctor

end
