module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation
public import stacks_project.Chap110.Lemma_110_43_1_Cotangent
public import stacks_project.Chap92.Lemma_92_4_2_Resolution
public import stacks_project.Chap92.Lemma_92_7_1_Omega
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Standard-resolution comparison for naive differentials

This leaf owns the simplicial evaluation of `omegaSheaf` on the standard polynomial
resolution, the degreewise tensor identification of `simplicialModule` with
`B ⊗[P] Ω[P ⁄ A]`, and the derived-category packaging of that comparison.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicTopology
open HomologicalComplex
open ComplexShape
open Algebra
open Algebra.PolynomialSite
open CommRingCat.Under.CotangentComplex
open CommAlgCat.Over.Polynomial.Site
open scoped Simplicial TensorProduct ChangeOfRings

noncomputable section

universe u q

namespace Algebra.CotangentComplex

/-- The object of `Under (CommRingCat.of A)` associated to an `A`-algebra `B`. -/
abbrev under (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Under (CommRingCat.of A) :=
  Under.mk (CommRingCat.ofHom (algebraMap A B))

/-- Unfolding of `under` as the under-object of `algebraMap A B`. -/
theorem under_eq (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    under A B = Under.mk (CommRingCat.ofHom (algebraMap A B)) :=
  sorry

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The degree-`n` polynomial arrow of the standard resolution of `B` over `A`. -/
abbrev standardPolynomial (n : SimplexCategoryᵒᵖ) : PolynomialOver A B :=
  (asPolynomialSimplicial (standardHom A B) (standard_isPolynomial A B)).obj n

/-- Unfolding `standardPolynomial` recovers the standard-resolution term as a polynomial
arrow. -/
theorem standardPolynomial_eq (n : SimplexCategoryᵒᵖ) :
    standardPolynomial A B n =
      (asPolynomialSimplicial (standardHom A B) (standard_isPolynomial A B)).obj n :=
  sorry

/-- The algebra structure on `B` induced by the standard-resolution augmentation in degree
`n`. -/
abbrev standardAlgebra (n : SimplexCategoryᵒᵖ) :
    Algebra (standardTerm (CommRingCat.of A) (under A B) n).right B :=
  RingHom.toAlgebra (standardAugmentation (CommRingCat.of A) (under A B) n).hom

/-- Unfolding `standardAlgebra` recovers `toAlgebra` of the standard-resolution
augmentation. -/
theorem standardAlgebra_eq (n : SimplexCategoryᵒᵖ) :
    standardAlgebra A B n =
      RingHom.toAlgebra (standardAugmentation (CommRingCat.of A) (under A B) n).hom :=
  sorry

/-- Evaluation of `omegaSheaf` on the standard polynomial resolution, as a simplicial
`B`-module. -/
def evalSimplicial : SimplicialObject (ModuleCat.{u} B) :=
  (CosimplicialObject.Evaluation.simplicial (ModuleCat.{u} B) (standardCosimplicial A B)).obj
    (omegaSheaf A B)

/-- Degreewise, `evalSimplicial` is `omegaSheaf` on the corresponding standard-resolution
site object. -/
theorem evalSimplicial_obj (n : SimplexCategoryᵒᵖ) :
    (evalSimplicial A B).obj n =
      (omegaSheaf A B).obj (op ((standardCosimplicial A B).obj n.unop)) :=
  sorry

/-- Identity from `omegaSheaf` on the standard cosimplicial object to `evalSimplicial`. -/
def omegaEvalHom (n : SimplexCategoryᵒᵖ) :
    (omegaSheaf A B).obj (op ((standardCosimplicial A B).obj n.unop)) ⟶
      (evalSimplicial A B).obj n :=
  𝟙 _

/-- Unfolding `omegaEvalHom` recovers the identity morphism. -/
theorem omegaEvalHom_eq (n : SimplexCategoryᵒᵖ) :
    omegaEvalHom A B n = 𝟙 _ :=
  sorry

/-- The standard cosimplicial object in degree `n` is the opposite polynomial arrow. -/
def standardCosimplicialHom (n : SimplexCategory) :
    ((standardCosimplicial A B : SimplexCategory ⥤ PolynomialSite A B).obj n) ⟶
      op (standardPolynomial A B (op n)) :=
  𝟙 _

/-- Unfolding `standardCosimplicialHom` recovers the identity morphism. -/
theorem standardCosimplicialHom_eq (n : SimplexCategory) :
    standardCosimplicialHom A B n = 𝟙 _ :=
  sorry

/-- Identity on carriers from the polynomial-arrow source to the standard-term ring. -/
def standardPolynomialCarrier (n : SimplexCategoryᵒᵖ) :
    (standardPolynomial A B n).obj.left →
      (standardTerm (CommRingCat.of A) (under A B) n).right :=
  fun x ↦ x

/-- Inverse identity on carriers from the standard-term ring to the polynomial-arrow
source. -/
def standardPolynomialCarrier_symm (n : SimplexCategoryᵒᵖ) :
    (standardTerm (CommRingCat.of A) (under A B) n).right →
      (standardPolynomial A B n).obj.left :=
  fun x ↦ x

/-- The two carrier identities compose to the identity on the polynomial-arrow source. -/
theorem standardPolynomialCarrier_left_inv (n : SimplexCategoryᵒᵖ)
    (x : (standardPolynomial A B n).obj.left) :
    standardPolynomialCarrier_symm A B n (standardPolynomialCarrier A B n x) = x :=
  sorry

/-- The two carrier identities compose to the identity on the standard-term ring. -/
theorem standardPolynomialCarrier_right_inv (n : SimplexCategoryᵒᵖ)
    (x : (standardTerm (CommRingCat.of A) (under A B) n).right) :
    standardPolynomialCarrier A B n (standardPolynomialCarrier_symm A B n x) = x :=
  sorry

/-- Identity on Kähler carriers of the polynomial-arrow source and the standard-term
ring. -/
def kaehlerCarrier (n : SimplexCategoryᵒᵖ) :
    KaehlerDifferential A (standardPolynomial A B n).obj.left →
      CommRingCat.KaehlerDifferential
        (standardTerm (CommRingCat.of A) (under A B) n).hom :=
  fun x ↦ x

/-- Inverse identity on Kähler carriers. -/
def kaehlerCarrier_symm (n : SimplexCategoryᵒᵖ) :
    CommRingCat.KaehlerDifferential
        (standardTerm (CommRingCat.of A) (under A B) n).hom →
      KaehlerDifferential A (standardPolynomial A B n).obj.left :=
  fun x ↦ x

/-- The relative Kähler module of a polynomial arrow is free, so `Ω_{O/A}` is `O`-flat and
`Li^* Ω_{O/A}` agrees with `i^* Ω_{O/A}`. -/
theorem kaehlerDifferential_free {X : PolynomialOver A B} :
    Module.Free X.obj.left (KaehlerDifferential A X.obj.left) :=
  sorry

/-- The relative Kähler module of a polynomial arrow is flat. -/
theorem kaehlerDifferential_flat {X : PolynomialOver A B} :
    Module.Flat X.obj.left (KaehlerDifferential A X.obj.left) :=
  sorry

/-- Degreewise tensor identification of the standard-resolution Kähler module with
`B ⊗[P] Ω[P ⁄ A]`. -/
def simplicialIso_obj (n : SimplexCategoryᵒᵖ) :=
  @ModuleCat.ExtendScalars.tensorIso
    (standardTerm (CommRingCat.of A) (under A B) n).right B _ _
    (standardAlgebra A B n)
    (CommRingCat.KaehlerDifferential (standardTerm (CommRingCat.of A) (under A B) n).hom)

/-- Unfolding `simplicialIso_obj` recovers `ModuleCat.ExtendScalars.tensorIso` of the
degree-`n` Kähler term. -/
theorem simplicialIso_obj_eq (n : SimplexCategoryᵒᵖ) :
    simplicialIso_obj A B n =
      @ModuleCat.ExtendScalars.tensorIso
        (standardTerm (CommRingCat.of A) (under A B) n).right B _ _
        (standardAlgebra A B n)
        (CommRingCat.KaehlerDifferential
          (standardTerm (CommRingCat.of A) (under A B) n).hom) :=
  sorry

/-- Ring homomorphism on carriers from a standard-resolution term to the corresponding
polynomial-arrow source. -/
def standardRingHom (n : SimplexCategory) :
    (standardTerm (CommRingCat.of A) (under A B) (op n)).right →+*
      (standardPolynomial A B (op n)).obj.left where
  toFun := standardPolynomialCarrier_symm A B (op n)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Ring homomorphism on carriers from a polynomial-arrow source to the corresponding
standard-resolution term. -/
def standardRingHom_symm (n : SimplexCategory) :
    (standardPolynomial A B (op n)).obj.left →+*
      (standardTerm (CommRingCat.of A) (under A B) (op n)).right where
  toFun := standardPolynomialCarrier A B (op n)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Identity on `B`, as a semilinear map along `standardRingHom`. -/
def idBSemilinear (n : SimplexCategory)
    [Algebra (standardTerm (CommRingCat.of A) (under A B) (op n)).right B]
    [Algebra (standardPolynomial A B (op n)).obj.left B] :
    B →ₛₗ[standardRingHom A B n] B where
  toFun := fun x ↦ x
  map_add' := fun _ _ ↦ sorry
  map_smul' := fun _ _ ↦ sorry

/-- Inverse identity on `B`, as a semilinear map along `standardRingHom_symm`. -/
def idBSemilinear_symm (n : SimplexCategory)
    [Algebra (standardPolynomial A B (op n)).obj.left B]
    [Algebra (standardTerm (CommRingCat.of A) (under A B) (op n)).right B] :
    B →ₛₗ[standardRingHom_symm A B n] B where
  toFun := fun x ↦ x
  map_add' := fun _ _ ↦ sorry
  map_smul' := fun _ _ ↦ sorry

/-- Semilinear identification of Kähler carriers along `standardRingHom`. -/
def kaehlerSemilinear (n : SimplexCategory) :
    (CommRingCat.KaehlerDifferential
        (standardTerm (CommRingCat.of A) (under A B) (op n)).hom : Type u) →ₛₗ[standardRingHom A B n]
      KaehlerDifferential A (standardPolynomial A B (op n)).obj.left where
  toFun := kaehlerCarrier_symm A B (op n)
  map_add' := fun _ _ ↦ sorry
  map_smul' := fun _ _ ↦ sorry

/-- Inverse semilinear identification of Kähler carriers along `standardRingHom_symm`. -/
def kaehlerSemilinear_symm (n : SimplexCategory) :
    KaehlerDifferential A (standardPolynomial A B (op n)).obj.left →ₛₗ[standardRingHom_symm A B n]
      (CommRingCat.KaehlerDifferential
        (standardTerm (CommRingCat.of A) (under A B) (op n)).hom : Type u) where
  toFun := kaehlerCarrier A B (op n)
  map_add' := fun _ _ ↦ sorry
  map_smul' := fun _ _ ↦ sorry

/-- Underlying function of the tensor identification with `omegaSheafObj`. -/
def omegaTensorMapFn (n : SimplexCategory)
    [Algebra (standardTerm (CommRingCat.of A) (under A B) (op n)).right B]
    [Algebra (standardPolynomial A B (op n)).obj.left B] :
    B ⊗[(standardTerm (CommRingCat.of A) (under A B) (op n)).right]
      (CommRingCat.KaehlerDifferential
        (standardTerm (CommRingCat.of A) (under A B) (op n)).hom) →
      B ⊗[(standardPolynomial A B (op n)).obj.left]
        KaehlerDifferential A (standardPolynomial A B (op n)).obj.left :=
  _root_.TensorProduct.map (idBSemilinear A B n) (kaehlerSemilinear A B n)

/-- Underlying inverse function of the tensor identification with `omegaSheafObj`. -/
def omegaTensorMapFn_symm (n : SimplexCategory)
    [Algebra (standardPolynomial A B (op n)).obj.left B]
    [Algebra (standardTerm (CommRingCat.of A) (under A B) (op n)).right B] :
    B ⊗[(standardPolynomial A B (op n)).obj.left]
      KaehlerDifferential A (standardPolynomial A B (op n)).obj.left →
      B ⊗[(standardTerm (CommRingCat.of A) (under A B) (op n)).right]
        (CommRingCat.KaehlerDifferential
          (standardTerm (CommRingCat.of A) (under A B) (op n)).hom) :=
  _root_.TensorProduct.map (idBSemilinear_symm A B n) (kaehlerSemilinear_symm A B n)

/-- Carrier-level map from the tensor presentation of the degree-`n` cotangent term to
`omegaSheafObj` of the corresponding standard polynomial arrow. -/
def omegaTensorHom (n : SimplexCategory)
    [Algebra (standardTerm (CommRingCat.of A) (under A B) (op n)).right B] :
    ModuleCat.of B
      (B ⊗[(standardTerm (CommRingCat.of A) (under A B) (op n)).right]
        (CommRingCat.KaehlerDifferential
          (standardTerm (CommRingCat.of A) (under A B) (op n)).hom)) ⟶
      omegaSheafObj (standardPolynomial A B (op n)) :=
  ModuleCat.ofHom
    { toFun := @omegaTensorMapFn A B _ _ _ n _ (algebraToBase (standardPolynomial A B (op n)))
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }

/-- Inverse carrier-level map from `omegaSheafObj` to the tensor presentation. -/
def omegaTensorInv (n : SimplexCategory)
    [Algebra (standardTerm (CommRingCat.of A) (under A B) (op n)).right B] :
    omegaSheafObj (standardPolynomial A B (op n)) ⟶
      ModuleCat.of B
        (B ⊗[(standardTerm (CommRingCat.of A) (under A B) (op n)).right]
          (CommRingCat.KaehlerDifferential
            (standardTerm (CommRingCat.of A) (under A B) (op n)).hom)) :=
  ModuleCat.ofHom
    { toFun := @omegaTensorMapFn_symm A B _ _ _ n (algebraToBase (standardPolynomial A B (op n))) _
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }

/-- Degreewise comparison of the tensor presentation with `omegaSheafObj`. -/
def omegaTensorIso (n : SimplexCategory)
    [Algebra (standardTerm (CommRingCat.of A) (under A B) (op n)).right B] :
    ModuleCat.of B
      (B ⊗[(standardTerm (CommRingCat.of A) (under A B) (op n)).right]
        (CommRingCat.KaehlerDifferential
          (standardTerm (CommRingCat.of A) (under A B) (op n)).hom)) ≅
      omegaSheafObj (standardPolynomial A B (op n)) where
  hom := omegaTensorHom A B n
  inv := omegaTensorInv A B n
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `omegaSheafMap` along the standard-cosimplicial identification in degree `n`. -/
def omegaSiteHom (n : SimplexCategory) :
    omegaSheafObj (standardPolynomial A B (op n)) ⟶
      (omegaSheaf A B).obj
        (op ((standardCosimplicial A B : SimplexCategory ⥤ PolynomialSite A B).obj n)) :=
  omegaSheafMap (standardCosimplicialHom A B n).unop

/-- Degreewise comparison of the standard-resolution simplicial module with
`evalSimplicial`. -/
def simplicialIsoApp (n : SimplexCategoryᵒᵖ) :
    (simplicialModule (CommRingCat.of A) (under A B)).obj n ≅
      (evalSimplicial A B).obj n where
  hom :=
    (simplicialIso_obj A B n).hom ≫
      @omegaTensorHom A B _ _ _ n.unop (standardAlgebra A B n) ≫
      omegaSiteHom A B n.unop ≫ omegaEvalHom A B n
  inv :=
    omegaEvalHom A B n ≫ omegaSiteHom A B n.unop ≫
      @omegaTensorInv A B _ _ _ n.unop (standardAlgebra A B n) ≫
      (simplicialIso_obj A B n).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Canonical comparison of simplicial `B`-modules between the cotangent-complex
simplicial module and evaluation of `omegaSheaf` on the standard resolution. -/
def simplicialIso :
    simplicialModule (CommRingCat.of A) (under A B) ≅ evalSimplicial A B :=
  NatIso.ofComponents (fun n ↦ simplicialIsoApp A B n) sorry

/-- The cochain complex of `evalSimplicial`, extended to integer degrees. -/
def evalCochain : CochainComplex (ModuleCat.{u} B) ℤ :=
  ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj (evalSimplicial A B)).extend
    embeddingDownNat

/-- Unfolding `evalCochain` recovers the extended alternating-face complex of
`evalSimplicial`. -/
theorem evalCochain_eq :
    evalCochain A B =
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj (evalSimplicial A B)).extend
        embeddingDownNat :=
  sorry

/-- In cohomological degree `-n`, `evalCochain` is the corresponding simplicial term of
`evalSimplicial`. -/
def evalCochainXIso (n : ℕ) :
    (evalCochain A B).X (-n) ≅ (evalSimplicial A B).obj (op ⦋n⦌) :=
  extendXIso ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj (evalSimplicial A B))
    embeddingDownNat (rfl : embeddingDownNat.f n = -n)

/-- Unfolding `evalCochainXIso` recovers `extendXIso` of the alternating-face complex. -/
theorem evalCochainXIso_eq (n : ℕ) :
    evalCochainXIso A B n =
      extendXIso ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj (evalSimplicial A B))
        embeddingDownNat (rfl : embeddingDownNat.f n = -n) :=
  sorry

/-- Cochain-level form of `simplicialIso`, after alternating faces and extension to
integer degrees. -/
def cochainIso :
    Algebra.cotangentComplex A B ≅ evalCochain A B :=
  (embeddingDownNat.extendFunctor (ModuleCat.{u} B)).mapIso
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).mapIso (simplicialIso A B))

/-- Unfolding `cochainIso` recovers extension of the alternating-face comparison. -/
theorem cochainIso_eq :
    cochainIso A B =
      (embeddingDownNat.extendFunctor (ModuleCat.{u} B)).mapIso
        ((alternatingFaceMapComplex (ModuleCat.{u} B)).mapIso (simplicialIso A B)) :=
  sorry

/-- In cohomological degree `-n`, `cochainIso` is the corresponding componentwise
comparison of cochain terms. -/
def cochainIso_X (n : ℕ) :
    (Algebra.cotangentComplex A B).X (-n) ≅ (evalCochain A B).X (-n) :=
  (HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.up ℤ) (-n)).mapIso
    (cochainIso A B)

variable [HasDerivedCategory.{q} (ModuleCat.{u} B)]

/-- Canonical identification of `L_{B/A}` with cosimplicial evaluation of `omegaSheaf`
on the standard resolution, as objects of `D(B)`. -/
def isoEval :
    DerivedCategory.Q.obj (Algebra.cotangentComplex A B) ≅
      (CosimplicialObject.Evaluation.toDerived (ModuleCat.{u} B)
        (standardCosimplicial A B)).obj (omegaSheaf A B) :=
  DerivedCategory.Q.mapIso (cochainIso A B)

/-- Unfolding `isoEval` recovers `DerivedCategory.Q.mapIso` of `cochainIso`. -/
theorem isoEval_eq :
    isoEval A B = DerivedCategory.Q.mapIso (cochainIso A B) :=
  sorry

end Algebra.CotangentComplex


