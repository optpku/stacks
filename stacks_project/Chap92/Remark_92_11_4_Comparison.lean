module

public import stacks_project.Chap92.«92_11_1_2_Comparison»

/-!
# Explicit cochain comparison from `L_{B/A}` to the naive cotangent complex

This leaf owns the cochain map `L_{B/A} ⟶ NL_{B/A}` attached to the standard
polynomial resolution of `B` over `A`. Degree `0` is the identification of
`Ω_{P₀/A} ⊗_{P₀} B` with the self-presentation `A[B]`, degree `-1` is the
face-difference map `Ω_{P₁/A} ⊗_{P₁} B ⟶ I/I²`, and the map vanishes in degrees
`≤ -2`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Opposite
open AlgebraicTopology
open scoped Simplicial ZeroObject TensorProduct ChangeOfRings

universe u

noncomputable section

namespace CategoryTheory.CommRingCat.Under
namespace CotangentComplex

open CommRingCat.Under.FreeAlgebra

/-- The canonical self-presentation `A[B] ⟶ B`. -/
abbrev selfHom (A : CommRingCat.{u}) (B : Under A) :
    (functor A).obj B.right ⟶ B :=
  (adjunction A).counit.app B

/-- Unfolding of `selfHom` as the free-forgetful counit. -/
theorem selfHom_eq (A : CommRingCat.{u}) (B : Under A) :
    selfHom A B = (adjunction A).counit.app B := sorry

/-- The naive cotangent complex of the self-presentation `A[B] ⟶ B`. -/
abbrev selfNaiveComplex (A : CommRingCat.{u}) (B : Under A) :
    CochainComplex (ModuleCat.{u} B.right) ℤ :=
  naiveComplex A B B.right (selfHom A B)

/-- Unfolding of `selfNaiveComplex` as `naiveComplex` of `selfHom`. -/
theorem selfNaiveComplex_eq (A : CommRingCat.{u}) (B : Under A) :
    selfNaiveComplex A B = naiveComplex A B B.right (selfHom A B) := sorry

/-- The `i`-th face map `dᵢ : P_{n+1} ⟶ Pₙ` of the standard polynomial resolution. -/
def standardFace (A : CommRingCat.{u}) (B : Under A) {n : ℕ} (i : Fin (n + 2)) :
    standardTerm A B (op ⦋n + 1⦌) ⟶ standardTerm A B (op ⦋n⦌) :=
  standardMap A B (SimplexCategory.δ i).op

/-- Unfolding of `standardFace` as `standardMap` of a coface. -/
theorem standardFace_eq (A : CommRingCat.{u}) (B : Under A) {n : ℕ} (i : Fin (n + 2)) :
    standardFace A B i = standardMap A B (SimplexCategory.δ i).op := sorry

/-- The face difference `d₀ x - d₁ x` as an element of `P₀`. -/
def faceSub (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right) :
    (standardTerm A B (op ⦋0⦌)).right :=
  (standardFace A B (0 : Fin 2)).right x - (standardFace A B (1 : Fin 2)).right x

/-- Unfolding of `faceSub` as the difference of the two faces `P₁ ⟶ P₀`. -/
theorem faceSub_eq (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right) :
    faceSub A B x =
      (standardFace A B (0 : Fin 2)).right x - (standardFace A B (1 : Fin 2)).right x :=
  sorry

/-- The face difference `d₀ x - d₁ x` lands in `I = Ker(A[B] ⟶ B)`. -/
theorem faceSub_mem_ker (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right) :
    faceSub A B x ∈ RingHom.ker (selfHom A B).right.hom := sorry

/-- The conormal class of `d₀ x - d₁ x` in `I/I²` as a module over `A[B]`. -/
def faceSubCotangent (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right) :
    naiveConormalRestrict A B B.right (selfHom A B) :=
  Ideal.toCotangent (RingHom.ker (selfHom A B).right.hom)
    ⟨faceSub A B x, faceSub_mem_ker A B x⟩

/-- Unfolding of `faceSubCotangent` as `Ideal.toCotangent` of the face difference. -/
theorem faceSubCotangent_eq (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right) :
    faceSubCotangent A B x =
      Ideal.toCotangent (RingHom.ker (selfHom A B).right.hom)
        ⟨faceSub A B x, faceSub_mem_ker A B x⟩ := sorry

/-- The `A`-derivation `P₁ ⟶ I/I²` sending `x` to the conormal class of `d₀ x - d₁ x`. -/
def faceDifferenceDerivation (A : CommRingCat.{u}) (B : Under A) :
    ((ModuleCat.restrictScalars (standardAugmentation A B (op ⦋1⦌)).hom).obj
      (naiveConormal A B B.right (selfHom A B))).Derivation
      (standardTerm A B (op ⦋1⦌)).hom :=
  ModuleCat.Derivation.mk
    (fun x =>
      ((1 : B.right) ⊗ₜ[((functor A).obj B.right).right, (selfHom A B).right.hom]
        (faceSubCotangent A B x) :
        (ModuleCat.restrictScalars (standardAugmentation A B (op ⦋1⦌)).hom).obj
          (naiveConormal A B B.right (selfHom A B))))
    (fun _ _ => sorry) (fun _ _ => sorry) (fun _ => sorry)

/-- The derivation `faceDifferenceDerivation` sends `x` to the class of `d₀ x - d₁ x`. -/
theorem faceDifferenceDerivation_apply (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right) :
    (faceDifferenceDerivation A B).d x =
      ((1 : B.right) ⊗ₜ[((functor A).obj B.right).right, (selfHom A B).right.hom]
        (faceSubCotangent A B x) :
        (ModuleCat.restrictScalars (standardAugmentation A B (op ⦋1⦌)).hom).obj
          (naiveConormal A B B.right (selfHom A B))) := sorry

/-- The degree `-1` downward arrow `Ω_{P₁/A} ⊗_{P₁} B ⟶ I/I²`. -/
def toConormal (A : CommRingCat.{u}) (B : Under A) :
    (simplicialModule A B).obj (op ⦋1⦌) ⟶
      naiveConormal A B B.right (selfHom A B) :=
  ((ModuleCat.extendRestrictScalarsAdj
      (standardAugmentation A B (op ⦋1⦌)).hom).homEquiv _ _).symm
    (faceDifferenceDerivation A B).desc

/-- Unfolding of `toConormal` as the adjunct of `faceDifferenceDerivation.desc`. -/
theorem toConormal_eq (A : CommRingCat.{u}) (B : Under A) :
    toConormal A B =
      ((ModuleCat.extendRestrictScalarsAdj
          (standardAugmentation A B (op ⦋1⦌)).hom).homEquiv _ _).symm
        (faceDifferenceDerivation A B).desc := sorry

/-- The generator formula: `toConormal` sends `d x` to the class of `d₀ x - d₁ x`. -/
theorem toConormal_tmul (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right) :
    ((ModuleCat.extendRestrictScalarsAdj
          (standardAugmentation A B (op ⦋1⦌)).hom).homEquiv _ _
        (toConormal A B))
        (CommRingCat.KaehlerDifferential.d x) =
      (faceDifferenceDerivation A B).d x := sorry

/-- The degree-zero self-presentation `P₀ ⟶ A[B]` used to identify Kähler differentials. -/
def selfToCounit (A : CommRingCat.{u}) (B : Under A) :
    standardTerm A B (op ⦋0⦌) ⟶ (functor A).obj B.right :=
  𝟙 _

/-- Unfolding of `selfToCounit` as the identity on `P₀ = A[B]`. -/
theorem selfToCounit_eq (A : CommRingCat.{u}) (B : Under A) :
    selfToCounit A B = 𝟙 _ := sorry

/-- Composing `selfToCounit` with the counit recovers the degree-zero augmentation. -/
theorem selfToCounit_comp_selfHom (A : CommRingCat.{u}) (B : Under A) :
    (standardAugmentation A B (op ⦋0⦌)).hom =
      (selfHom A B).right.hom.comp (selfToCounit A B).right.hom := sorry

/-- Degree-`0` identification `Ω_{P₀/A} ⊗_{P₀} B ⟶ Ω_{A[B]/A} ⊗_{A[B]} B`. -/
def selfDifferentials (A : CommRingCat.{u}) (B : Under A) :
    (simplicialModule A B).obj (op ⦋0⦌) ⟶
      naiveDifferentials A B B.right (selfHom A B) :=
  ((ModuleCat.extendRestrictScalarsAdj
      (standardAugmentation A B (op ⦋0⦌)).hom).homEquiv _ _).symm
    (CommRingCat.KaehlerDifferential.map
        ((Category.id_comp ((functor A).obj B.right).hom).trans (selfToCounit A B).w.symm) ≫
      (ModuleCat.restrictScalars (selfToCounit A B).right.hom).map
        ((ModuleCat.extendRestrictScalarsAdj (selfHom A B).right.hom).unit.app _) ≫
      (ModuleCat.restrictScalarsComp'
        (selfToCounit A B).right.hom
        (selfHom A B).right.hom
        (standardAugmentation A B (op ⦋0⦌)).hom
        (selfToCounit_comp_selfHom A B)).inv.app _)

/-- Unfolding of `selfDifferentials` as the adjunct of the identity-square Kähler map. -/
theorem selfDifferentials_eq (A : CommRingCat.{u}) (B : Under A) :
    selfDifferentials A B =
      ((ModuleCat.extendRestrictScalarsAdj
          (standardAugmentation A B (op ⦋0⦌)).hom).homEquiv _ _).symm
        (CommRingCat.KaehlerDifferential.map
            ((Category.id_comp ((functor A).obj B.right).hom).trans
              (selfToCounit A B).w.symm) ≫
          (ModuleCat.restrictScalars (selfToCounit A B).right.hom).map
            ((ModuleCat.extendRestrictScalarsAdj (selfHom A B).right.hom).unit.app _) ≫
          (ModuleCat.restrictScalarsComp'
            (selfToCounit A B).right.hom
            (selfHom A B).right.hom
            (standardAugmentation A B (op ⦋0⦌)).hom
            (selfToCounit_comp_selfHom A B)).inv.app _) := sorry

/-- Components of the explicit cochain map `L_{B/A} ⟶ NL_{B/A}`. -/
def toNaive_f (A : CommRingCat.{u}) (B : Under A) :
    ∀ i : ℤ, (obj A B).X i ⟶ (selfNaiveComplex A B).X i
  | Int.ofNat 0 =>
      (objXIso A B 0).hom ≫
        selfDifferentials A B ≫
        (naiveComplex_X_zero A B B.right (selfHom A B)).inv
  | Int.negSucc 0 =>
      (objXIso A B 1).hom ≫
        toConormal A B ≫
        (naiveComplex_X_negOne A B B.right (selfHom A B)).inv
  | Int.negSucc (_n + 1) => 0
  | Int.ofNat (_n + 1) => 0

/-- The explicit cochain map `L_{B/A} ⟶ NL_{B/A}` of the standard resolution. -/
def toNaive (A : CommRingCat.{u}) (B : Under A) :
    obj A B ⟶ selfNaiveComplex A B where
  f := toNaive_f A B
  comm' := sorry

/-- Unfolding of the components of `toNaive`. -/
theorem toNaive_f_eq (A : CommRingCat.{u}) (B : Under A) (i : ℤ) :
    (toNaive A B).f i = toNaive_f A B i := sorry

/-- Degree `0` of `toNaive` is the identification of `Ω_{P₀/A} ⊗_{P₀} B`. -/
theorem toNaive_f_zero (A : CommRingCat.{u}) (B : Under A) :
    (toNaive A B).f 0 =
      (objXIso A B 0).hom ≫
        selfDifferentials A B ≫
        (naiveComplex_X_zero A B B.right (selfHom A B)).inv := sorry

/-- Degree `-1` of `toNaive` is the face-difference map `toConormal`. -/
theorem toNaive_f_negOne (A : CommRingCat.{u}) (B : Under A) :
    (toNaive A B).f (-1) =
      (objXIso A B 1).hom ≫
        toConormal A B ≫
        (naiveComplex_X_negOne A B B.right (selfHom A B)).inv := sorry

end CotangentComplex
end CategoryTheory.CommRingCat.Under
