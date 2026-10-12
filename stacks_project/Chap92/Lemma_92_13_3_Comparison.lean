/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_13_0_1»
public import stacks_project.Chap92.Lemma_92_13_2_Biderivation
public import stacks_project.Chap92.Remark_92_11_4_Comparison
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Comparison of `L_{B/A}` with the Lichtenbaum–Schlessinger complex

This leaf owns the cochain map `L_{B/A} ⟶ LS(P)` attached to a polynomial
presentation `P`. Degree `0` is `dψ ⊗ 1` for the canonical lift `ψ` of `P.σ`,
degree `-1` is the ordinary derivation associated to the biderivation `λ`,
degree `-2` sends `dg` to the class of `λ(d₀ g - d₁ g + d₂ g)` in `Rel/TrivRel`,
and the map vanishes in all other degrees.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Opposite
open AlgebraicTopology
open Algebra.Presentation
open scoped Simplicial ZeroObject TensorProduct

universe u

noncomputable section

namespace Algebra.Presentation.LichtenbaumSchlessinger

open CommRingCat.Under.CotangentComplex
open CommRingCat.Under.FreeAlgebra (adjunction generator polynomialIso)

variable {A B ι σ : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The object of `Under A` associated to the algebra `B`. -/
def under (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Under (CommRingCat.of A) :=
  Under.mk (CommRingCat.ofHom (algebraMap A B))

/-- Unfolding of `under` as the under-object of `algebraMap A B`. -/
theorem under_eq (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    under A B = Under.mk (CommRingCat.ofHom (algebraMap A B)) := sorry

/-- The object of `Under A` associated to the polynomial ring of a presentation. -/
def underPoly (P : Presentation A B ι σ) : Under (CommRingCat.of A) :=
  Under.mk (CommRingCat.ofHom (algebraMap A P.Ring))

/-- Unfolding of `underPoly` as the under-object of `algebraMap A P.Ring`. -/
theorem underPoly_eq (P : Presentation A B ι σ) :
    underPoly P = Under.mk (CommRingCat.ofHom (algebraMap A P.Ring)) := sorry

/-- The canonical `A`-algebra map `ψ : P₀ ⟶ P.Ring` induced by the section `P.σ`. -/
def toPolynomial (P : Presentation A B ι σ) :
    standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌) ⟶ underPoly P :=
  ((adjunction (CommRingCat.of A)).homEquiv B (underPoly P)).symm (TypeCat.ofHom P.σ)

/-- Unfolding of `toPolynomial` as the adjunct of `P.σ`. -/
theorem toPolynomial_eq (P : Presentation A B ι σ) :
    toPolynomial P =
      ((adjunction (CommRingCat.of A)).homEquiv B (underPoly P)).symm (TypeCat.ofHom P.σ) :=
  sorry

/-- The lift `ψ` is compatible with the augmentations `P₀ ⟶ B` and `P.Ring ⟶ B`. -/
theorem toPolynomial_comp_algebraMap (P : Presentation A B ι σ) :
    (standardAugmentation (CommRingCat.of A) (under A B) (op ⦋0⦌)).hom =
      (algebraMap P.Ring B).comp (toPolynomial P).right.hom := sorry

/-- The `P.Ring`-linear combination map `F ⟶ I` on the relation generators. -/
def relationCombination (P : Presentation A B ι σ) : free P →ₗ[P.Ring] P.ker :=
  (LinearEquiv.ofEq
      (LinearMap.range (Finsupp.linearCombination P.Ring P.relation))
      P.ker
      ((Finsupp.range_linearCombination P.Ring).trans
        P.span_range_relation_eq_ker)).toLinearMap.comp
    (Finsupp.linearCombination P.Ring P.relation).rangeRestrict

/-- Unfolding of `relationCombination` as the range restriction of evaluation on
`P.relation`, transported along the identification of the span with `P.ker`. -/
theorem relationCombination_eq (P : Presentation A B ι σ) :
    relationCombination P =
      (LinearEquiv.ofEq
          (LinearMap.range (Finsupp.linearCombination P.Ring P.relation))
          P.ker
          ((Finsupp.range_linearCombination P.Ring).trans
            P.span_range_relation_eq_ker)).toLinearMap.comp
        (Finsupp.linearCombination P.Ring P.relation).rangeRestrict := sorry

/-- Evaluation on the relation generators is surjective onto `P.ker`. -/
theorem relationCombination_surjective (P : Presentation A B ι σ) :
    Function.Surjective (relationCombination P) := sorry

/-- A chosen `P.Ring`-linear section of `F ⟶ I`. -/
def relationSection (P : Presentation A B ι σ) : P.ker → free P :=
  fun x ↦
    Function.surjInv
      (LinearMap.surjective_rangeRestrict
        (Finsupp.linearCombination P.Ring P.relation))
      ((LinearEquiv.ofEq
          (LinearMap.range (Finsupp.linearCombination P.Ring P.relation))
          P.ker
          ((Finsupp.range_linearCombination P.Ring).trans
            P.span_range_relation_eq_ker)).symm x)

/-- The chosen section of `F ⟶ I` is a right inverse of `relationCombination`. -/
theorem relationSection_spec (P : Presentation A B ι σ) (x : P.ker) :
    relationCombination P (relationSection P x) = x := sorry

/-- The image of `ψ(d₀ x - d₁ x)` in the kernel `I = ker(P.Ring ⟶ B)`. -/
def toKer (P : Presentation A B ι σ)
    (x : (standardTerm (CommRingCat.of A) (under A B) (op ⦋1⦌)).right) :
    P.ker :=
  ⟨(toPolynomial P).right
      (faceSub (CommRingCat.of A) (under A B) x),
    sorry⟩

/-- Unfolding of `toKer` as the subtype of `ψ(d₀ x - d₁ x)`. -/
theorem toKer_eq (P : Presentation A B ι σ)
    (x : (standardTerm (CommRingCat.of A) (under A B) (op ⦋1⦌)).right) :
    (toKer P x : P.Ring) =
      (toPolynomial P).right (faceSub (CommRingCat.of A) (under A B) x) :=
  sorry

/-- Assigned generator values of the polynomial model of `P₁`, obtained by lifting
`ψ(d₀ X_s - d₁ X_s)` along `F ⟶ I`. -/
def generatorValue (P : Presentation A B ι σ)
    (s : (standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) :
    free P :=
  relationSection P (toKer P (generator (CommRingCat.of A) s))

/-- Unfolding of `generatorValue` as the chosen section of `ψ(d₀ X_s - d₁ X_s)`. -/
theorem generatorValue_eq (P : Presentation A B ι σ)
    (s : (standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) :
    generatorValue P s =
      relationSection P (toKer P (generator (CommRingCat.of A) s)) := sorry

/-- The left structure map `ψ ∘ d₀` on the polynomial model of `P₁`. -/
def leftHom (P : Presentation A B ι σ) :
    MvPolynomial
      ((standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) A →+*
      P.Ring :=
  MvPolynomial.eval₂Hom (algebraMap A P.Ring)
    (fun s ↦
      (toPolynomial P).right
        ((standardFace (CommRingCat.of A) (under A B) (0 : Fin 2)).right
          (generator (CommRingCat.of A) s)))

/-- Unfolding of `leftHom` as evaluation at `ψ ∘ d₀` on the universal generators. -/
theorem leftHom_eq (P : Presentation A B ι σ) :
    leftHom P =
      MvPolynomial.eval₂Hom (algebraMap A P.Ring)
        (fun s ↦
          (toPolynomial P).right
            ((standardFace (CommRingCat.of A) (under A B) (0 : Fin 2)).right
              (generator (CommRingCat.of A) s))) :=
  sorry

/-- The right structure map `ψ ∘ d₁` on the polynomial model of `P₁`. -/
def rightHom (P : Presentation A B ι σ) :
    MvPolynomial
      ((standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) A →+*
      P.Ring :=
  MvPolynomial.eval₂Hom (algebraMap A P.Ring)
    (fun s ↦
      (toPolynomial P).right
        ((standardFace (CommRingCat.of A) (under A B) (1 : Fin 2)).right
          (generator (CommRingCat.of A) s)))

/-- Unfolding of `rightHom` as evaluation at `ψ ∘ d₁` on the universal generators. -/
theorem rightHom_eq (P : Presentation A B ι σ) :
    rightHom P =
      MvPolynomial.eval₂Hom (algebraMap A P.Ring)
        (fun s ↦
          (toPolynomial P).right
            ((standardFace (CommRingCat.of A) (under A B) (1 : Fin 2)).right
              (generator (CommRingCat.of A) s))) := sorry

/-- The left `P₁`-module structure on `F` via `ψ ∘ d₀`. -/
instance instModuleLeft (P : Presentation A B ι σ) :
    Module
      (MvPolynomial
        ((standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) A)
      (free P) :=
  Module.compHom (free P) (leftHom P)

/-- The right `P₁`-module structure on `F` via `ψ ∘ d₁`. -/
instance instModuleRight (P : Presentation A B ι σ) :
    Module
      (MvPolynomial
          ((standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) A)ᵐᵒᵖ
      (free P) :=
  Module.compHom (free P) (RingHom.op (rightHom P))

/-- The left `P₁`-action on `F` extends the `A`-action. -/
instance instIsScalarTowerLeft (P : Presentation A B ι σ) :
    IsScalarTower A
      (MvPolynomial
        ((standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) A)
      (free P) :=
  sorry

/-- The opposite `P₁`-action on `F` extends the `A`-action. -/
instance instIsScalarTowerRight (P : Presentation A B ι σ) :
    IsScalarTower A
      (MvPolynomial
          ((standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) A)ᵐᵒᵖ
      (free P) :=
  sorry

/-- The left and opposite `P₁`-actions on `F` commute. -/
instance instSMulCommClass (P : Presentation A B ι σ) :
    SMulCommClass
      (MvPolynomial
        ((standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) A)
      (MvPolynomial
          ((standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) A)ᵐᵒᵖ
      (free P) :=
  sorry

/-- Generator values of the polynomial biderivation satisfy the commuting-variable relation. -/
theorem generatorValue_compatible (P : Presentation A B ι σ) :
    MvPolynomial.BiderivationCompatible A (generatorValue P) := sorry

/-- The unique polynomial `A`-biderivation `λ : A[P₀] ⟶ F` with the assigned generator values. -/
def biderivation (P : Presentation A B ι σ) :
    Biderivation A
      (MvPolynomial
        ((standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) A)
      (free P) :=
  MvPolynomial.mkBiderivation A (generatorValue P) (generatorValue_compatible P)

/-- The polynomial biderivation realizes the assigned generator values. -/
theorem biderivation_X (P : Presentation A B ι σ)
    (s : (standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) :
    (biderivation P).toLinearMap (MvPolynomial.X s) = generatorValue P s := sorry

/-- The polynomial representative of an element of `P₁`, the forward map of
`polynomialIso`. -/
def toPolynomialModel
    (x : (standardTerm (CommRingCat.of A) (under A B) (op ⦋1⦌)).right) :
    MvPolynomial
      ((standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) A :=
  (CommRingCat.Under.FreeAlgebra.toPolynomial (CommRingCat.of A)
      ((standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right)).right x

/-- Unfolding of `toPolynomialModel` as the forward component of `polynomialIso`. -/
theorem toPolynomialModel_eq
    (x : (standardTerm (CommRingCat.of A) (under A B) (op ⦋1⦌)).right) :
    toPolynomialModel x =
      (polynomialIso (CommRingCat.of A)
          ((standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right)).hom.right x :=
  sorry

/-- The polynomial comparison sends the universal generator `X_s` to the variable `X s`. -/
theorem toPolynomialModel_generator
    (s : (standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) :
    toPolynomialModel (generator (CommRingCat.of A) s) = MvPolynomial.X s := sorry

/-- The `A`-biderivation `λ : P₁ ⟶ F` obtained by transporting `biderivation` along
`polynomialIso`. -/
def biderivationApply (P : Presentation A B ι σ)
    (x : (standardTerm (CommRingCat.of A) (under A B) (op ⦋1⦌)).right) :
    free P :=
  (biderivation P).apply (toPolynomialModel x)

/-- Unfolding of `biderivationApply` as the transported polynomial biderivation. -/
theorem biderivationApply_eq (P : Presentation A B ι σ)
    (x : (standardTerm (CommRingCat.of A) (under A B) (op ⦋1⦌)).right) :
    biderivationApply P x = (biderivation P).apply (toPolynomialModel x) := sorry

/-- On universal generators, the transported biderivation recovers the assigned section. -/
theorem biderivationApply_generator (P : Presentation A B ι σ)
    (s : (standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) :
    biderivationApply P (generator (CommRingCat.of A) s) = generatorValue P s := sorry

/-- The ordinary `A`-derivation `P₀ ⟶ Ω_{P/A} ⊗_P B` sending `x` to `1 ⊗ D(ψ x)`. -/
def toDifferentialsDerivation (P : Presentation A B ι σ) :
    ((ModuleCat.restrictScalars
          (standardAugmentation (CommRingCat.of A) (under A B)
            (op ⦋0⦌)).hom).obj
        (ModuleCat.of B P.toExtension.CotangentSpace)).Derivation
      (standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).hom :=
  ModuleCat.Derivation.mk
    (fun x ↦
      (1 : B) ⊗ₜ[P.toExtension.Ring]
        (_root_.KaehlerDifferential.D A P.toExtension.Ring ((toPolynomial P).right x)))
    (fun _ _ ↦ sorry) (fun _ _ ↦ sorry) (fun _ ↦ sorry)

/-- The derivation `toDifferentialsDerivation` sends `x` to `1 ⊗ D(ψ x)`. -/
theorem toDifferentialsDerivation_apply (P : Presentation A B ι σ)
    (x : (standardTerm (CommRingCat.of A) (under A B) (op ⦋0⦌)).right) :
    (toDifferentialsDerivation P).d x =
      (1 : B) ⊗ₜ[P.toExtension.Ring]
        (_root_.KaehlerDifferential.D A P.toExtension.Ring ((toPolynomial P).right x)) := sorry

/-- Degree-`0` comparison `Ω_{P₀/A} ⊗_{P₀} B ⟶ Ω_{P/A} ⊗_P B`. -/
def toDifferentials (P : Presentation A B ι σ) :
    (simplicialModule (CommRingCat.of A) (under A B)).obj (op ⦋0⦌) ⟶
      ModuleCat.of B P.toExtension.CotangentSpace :=
  ((ModuleCat.extendRestrictScalarsAdj
        (standardAugmentation (CommRingCat.of A) (under A B)
          (op ⦋0⦌)).hom).homEquiv _ _).symm
    (toDifferentialsDerivation P).desc

/-- Unfolding of `toDifferentials` as the adjunct of `toDifferentialsDerivation.desc`. -/
theorem toDifferentials_eq (P : Presentation A B ι σ) :
    toDifferentials P =
      ((ModuleCat.extendRestrictScalarsAdj
            (standardAugmentation (CommRingCat.of A) (under A B)
              (op ⦋0⦌)).hom).homEquiv _ _).symm
        (toDifferentialsDerivation P).desc := sorry

/-- The ordinary `A`-derivation `P₁ ⟶ F ⊗ B` associated to `λ`. -/
def toFreeDerivation (P : Presentation A B ι σ) :
    ((ModuleCat.restrictScalars
          (standardAugmentation (CommRingCat.of A) (under A B)
            (op ⦋1⦌)).hom).obj
        (ModuleCat.of B (B ⊗[P.Ring] free P))).Derivation
      (standardTerm (CommRingCat.of A) (under A B) (op ⦋1⦌)).hom :=
  ModuleCat.Derivation.mk
    (fun x ↦ (1 : B) ⊗ₜ[P.Ring] biderivationApply P x)
    (fun _ _ ↦ sorry) (fun _ _ ↦ sorry) (fun _ ↦ sorry)

/-- The derivation `toFreeDerivation` sends `x` to `1 ⊗ λ(x)`. -/
theorem toFreeDerivation_apply (P : Presentation A B ι σ)
    (x : (standardTerm (CommRingCat.of A) (under A B) (op ⦋1⦌)).right) :
    (toFreeDerivation P).d x = (1 : B) ⊗ₜ[P.Ring] biderivationApply P x := sorry

/-- Degree-`-1` comparison `Ω_{P₁/A} ⊗_{P₁} B ⟶ F ⊗_P B`. -/
def toFreeMap (P : Presentation A B ι σ) :
    (simplicialModule (CommRingCat.of A) (under A B)).obj (op ⦋1⦌) ⟶
      ModuleCat.of B (B ⊗[P.Ring] free P) :=
  ((ModuleCat.extendRestrictScalarsAdj
        (standardAugmentation (CommRingCat.of A) (under A B)
          (op ⦋1⦌)).hom).homEquiv _ _).symm
    (toFreeDerivation P).desc

/-- Unfolding of `toFreeMap` as the adjunct of `toFreeDerivation.desc`. -/
theorem toFreeMap_eq (P : Presentation A B ι σ) :
    toFreeMap P =
      ((ModuleCat.extendRestrictScalarsAdj
            (standardAugmentation (CommRingCat.of A) (under A B)
              (op ⦋1⦌)).hom).homEquiv _ _).symm
        (toFreeDerivation P).desc := sorry

/-- The alternating face combination `d₀ g - d₁ g + d₂ g` on `P₂`. -/
def faceAlt
    (g : (standardTerm (CommRingCat.of A) (under A B) (op ⦋2⦌)).right) :
    (standardTerm (CommRingCat.of A) (under A B) (op ⦋1⦌)).right :=
  (standardFace (CommRingCat.of A) (under A B) (0 : Fin 3)).right g -
    (standardFace (CommRingCat.of A) (under A B) (1 : Fin 3)).right g +
      (standardFace (CommRingCat.of A) (under A B) (2 : Fin 3)).right g

/-- Unfolding of `faceAlt` as the alternating sum of the three faces `P₂ ⟶ P₁`. -/
theorem faceAlt_eq
    (g : (standardTerm (CommRingCat.of A) (under A B) (op ⦋2⦌)).right) :
    faceAlt g =
      (standardFace (CommRingCat.of A) (under A B) (0 : Fin 3)).right g -
        (standardFace (CommRingCat.of A) (under A B) (1 : Fin 3)).right g +
          (standardFace (CommRingCat.of A) (under A B) (2 : Fin 3)).right g :=
  sorry

/-- The image of `λ(d₀ g - d₁ g + d₂ g)` in `Rel`. -/
def toRel (P : Presentation A B ι σ)
    (g : (standardTerm (CommRingCat.of A) (under A B) (op ⦋2⦌)).right) :
    rel P :=
  ⟨biderivationApply P (faceAlt g), sorry⟩

/-- Unfolding of `toRel` as the subtype of `λ(d₀ g - d₁ g + d₂ g)`. -/
theorem toRel_eq (P : Presentation A B ι σ)
    (g : (standardTerm (CommRingCat.of A) (under A B) (op ⦋2⦌)).right) :
    (toRel P g : free P) = biderivationApply P (faceAlt g) := sorry

/-- The ordinary `A`-derivation `P₂ ⟶ Rel/TrivRel ⊗ B` sending `g` to the class of
`λ(d₀ g - d₁ g + d₂ g)`. -/
def toRelDerivation (P : Presentation A B ι σ) :
    ((ModuleCat.restrictScalars
          (standardAugmentation (CommRingCat.of A) (under A B)
            (op ⦋2⦌)).hom).obj
        (ModuleCat.of B (B ⊗[P.Ring] relModTrivial P))).Derivation
      (standardTerm (CommRingCat.of A) (under A B) (op ⦋2⦌)).hom :=
  ModuleCat.Derivation.mk
    (fun g ↦ (1 : B) ⊗ₜ[P.Ring] (Submodule.Quotient.mk (toRel P g)))
    (fun _ _ ↦ sorry) (fun _ _ ↦ sorry) (fun _ ↦ sorry)

/-- The derivation `toRelDerivation` sends `g` to the class of `λ(d₀ g - d₁ g + d₂ g)`. -/
theorem toRelDerivation_apply (P : Presentation A B ι σ)
    (g : (standardTerm (CommRingCat.of A) (under A B) (op ⦋2⦌)).right) :
    (toRelDerivation P).d g =
      (1 : B) ⊗ₜ[P.Ring] (Submodule.Quotient.mk (toRel P g)) := sorry

/-- Degree-`-2` comparison `Ω_{P₂/A} ⊗_{P₂} B ⟶ Rel/TrivRel ⊗_P B`. -/
def toRelMap (P : Presentation A B ι σ) :
    (simplicialModule (CommRingCat.of A) (under A B)).obj (op ⦋2⦌) ⟶
      ModuleCat.of B (B ⊗[P.Ring] relModTrivial P) :=
  ((ModuleCat.extendRestrictScalarsAdj
        (standardAugmentation (CommRingCat.of A) (under A B)
          (op ⦋2⦌)).hom).homEquiv _ _).symm
    (toRelDerivation P).desc

/-- Unfolding of `toRelMap` as the adjunct of `toRelDerivation.desc`. -/
theorem toRelMap_eq (P : Presentation A B ι σ) :
    toRelMap P =
      ((ModuleCat.extendRestrictScalarsAdj
            (standardAugmentation (CommRingCat.of A) (under A B)
              (op ⦋2⦌)).hom).homEquiv _ _).symm
        (toRelDerivation P).desc := sorry

/-- Components of the cochain comparison `L_{B/A} ⟶ LS(P)`. -/
def toComplex_f (P : Presentation A B ι σ) :
    ∀ i : ℤ,
      (Algebra.cotangentComplex A B).X i ⟶ (complex P).X i
  | Int.ofNat 0 =>
      (objXIso (CommRingCat.of A) (under A B) 0).hom ≫
        toDifferentials P ≫ (complex_X_zero P).inv
  | Int.negSucc 0 =>
      (objXIso (CommRingCat.of A) (under A B) 1).hom ≫
        toFreeMap P ≫ (complex_X_negOne P).inv
  | Int.negSucc 1 =>
      (objXIso (CommRingCat.of A) (under A B) 2).hom ≫
        toRelMap P ≫ (complex_X_negTwo P).inv
  | Int.negSucc (_n + 2) => 0
  | Int.ofNat (_n + 1) => 0

/-- The canonical cochain map `L_{B/A} ⟶ LS(P)` of a polynomial presentation. -/
def toComplex (P : Presentation A B ι σ) :
    Algebra.cotangentComplex A B ⟶ complex P where
  f := toComplex_f P
  comm' := sorry

/-- Unfolding of the components of `toComplex`. -/
theorem toComplex_f_eq (P : Presentation A B ι σ) (i : ℤ) :
    (toComplex P).f i = toComplex_f P i := sorry

/-- Degree `0` of `toComplex` is the Kähler map of `ψ`. -/
theorem toComplex_f_zero (P : Presentation A B ι σ) :
    (toComplex P).f 0 =
      (objXIso (CommRingCat.of A) (under A B) 0).hom ≫
        toDifferentials P ≫ (complex_X_zero P).inv := sorry

/-- Degree `-1` of `toComplex` is the ordinary derivation associated to `λ`. -/
theorem toComplex_f_negOne (P : Presentation A B ι σ) :
    (toComplex P).f (-1) =
      (objXIso (CommRingCat.of A) (under A B) 1).hom ≫
        toFreeMap P ≫ (complex_X_negOne P).inv := sorry

/-- Degree `-2` of `toComplex` sends `dg` to the class of `λ(d₀ g - d₁ g + d₂ g)`. -/
theorem toComplex_f_negTwo (P : Presentation A B ι σ) :
    (toComplex P).f (-2) =
      (objXIso (CommRingCat.of A) (under A B) 2).hom ≫
        toRelMap P ≫ (complex_X_negTwo P).inv := sorry

/-- The Lichtenbaum–Schlessinger complex is strictly concentrated in degrees `≥ -2`. -/
instance complex_isStrictlyGE_negTwo (P : Presentation A B ι σ) :
    (complex P).IsStrictlyGE (-2) := sorry

/-- The Lichtenbaum–Schlessinger complex is concentrated in degrees `≥ -2`. -/
instance complex_isGE_negTwo (P : Presentation A B ι σ) :
    (complex P).IsGE (-2) := sorry

/-- After `τ_{≥ -2}`, the comparison `L_{B/A} ⟶ LS(P)` is a quasi-isomorphism. -/
instance toComplex_truncGE_quasiIso (P : Presentation A B ι σ) :
    QuasiIso (CochainComplex.truncGEMap (toComplex P) (-2)) := sorry

/-- The truncated comparison is a quasi-isomorphism in every degree `i ≥ -2`. -/
theorem toComplex_quasiIsoAt (P : Presentation A B ι σ) (i : ℤ) (hi : -2 ≤ i) :
    QuasiIsoAt (toComplex P) i := sorry

end Algebra.Presentation.LichtenbaumSchlessinger
