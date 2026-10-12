/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import ReasLib.Algebra.Category.CommAlgCat.IndEtale.Objects
public import ReasLib.RingTheory.RingHom.IndEtale.BaseChange

@[expose] public section

open CategoryTheory TensorProduct

universe v w u

namespace CommAlgCat.IndEtale

/-- Tensor-product base change preserves ind-étaleness. -/
theorem baseChange_indEtale (R : Type u) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]
    (A : IndEtale.{v} R) :
    (algebraMap S (S ⊗[R] A)).IndEtale := sorry

/-- Tensor-product base change on ind-étale algebras. -/
def baseChange (R : Type u) [CommRing R] (S : Type w) [CommRing S] [Algebra R S] :
    IndEtale.{v} R ⥤ IndEtale.{max w v} S where
  obj A :=
    { obj := .of S (S ⊗[R] A)
      property := baseChange_indEtale R S A }
  map {A B} f :=
    { hom := CommAlgCat.ofHom (Algebra.TensorProduct.map (.id _ _) f.hom.hom) }

/-- The underlying algebra of a base change is the tensor product. -/
theorem baseChange_obj (R : Type u) [CommRing R] (S : Type w) [CommRing S] [Algebra R S]
    (A : IndEtale.{v} R) :
    ((baseChange.{v} R S).obj A).obj = .of S (S ⊗[R] A) := rfl

/-- Reduction modulo `I` on ind-étale algebras is the canonical base-change functor along
`A → A ⧸ I`. -/
abbrev reduction {A : Type u} [CommRing A] (I : Ideal A) :
    IndEtale.{u} A ⥤ IndEtale.{u} (A ⧸ I) :=
  baseChange A (A ⧸ I)

/-- Reduction is base change along `A → A ⧸ I`. -/
theorem reduction_eq {A : Type u} [CommRing A] (I : Ideal A) :
    reduction I = baseChange A (A ⧸ I) := rfl

/-- Reduction of an ind-étale `A`-algebra `C` is identified with `C ⧸ I C`. -/
noncomputable def reductionObjQuotEquiv {A : Type u} [CommRing A] (I : Ideal A)
    (C : IndEtale.{u} A) :
    ((reduction I).obj C) ≃ₐ[A ⧸ I] (C ⧸ Ideal.map (algebraMap A C) I) :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I).symm

/-- The reduction comparison is the inverse of the tensor-quotient algebra equivalence. -/
theorem reductionObjQuotEquiv_symm {A : Type u} [CommRing A] (I : Ideal A)
    (C : IndEtale.{u} A) :
    (reductionObjQuotEquiv I C).symm = Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I :=
  (AlgEquiv.symm_symm _).symm

end CommAlgCat.IndEtale
