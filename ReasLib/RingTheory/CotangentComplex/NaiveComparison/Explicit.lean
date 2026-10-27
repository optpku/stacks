/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.NaiveComparison.IsIso

/-!
# Explicit comparison with the naive cotangent complex

The standard polynomial resolution of a commutative algebra gives a cochain map
from its cotangent complex to the naive complex of the self-presentation
`A[B] ⟶ B`. In degree zero it is the canonical identification of differentials;
in degree minus one it is induced by the difference of the first two faces;
all other components vanish.

The self-presentation is surjective. Consequently its scalar-extended conormal
module `B ⊗_{A[B]} (I/I²)` canonically represents `I/I²` as a `B`-module.
The construction retains this scalar-extended model rather than identifying it
literally with the underlying `A[B]`-module. Analogous comparisons for ringed
sites require additional identifications with these ring-level models.
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
    selfHom A B = (adjunction A).counit.app B := rfl

/-- The naive cotangent complex of the self-presentation `A[B] ⟶ B`. -/
abbrev selfNaiveComplex (A : CommRingCat.{u}) (B : Under A) :
    CochainComplex (ModuleCat.{u} B.right) ℤ :=
  naiveComplex A B B.right (selfHom A B)

/-- Unfolding of `selfNaiveComplex` as `naiveComplex` of `selfHom`. -/
theorem selfNaiveComplex_eq (A : CommRingCat.{u}) (B : Under A) :
    selfNaiveComplex A B = naiveComplex A B B.right (selfHom A B) := rfl

/-- The `i`-th face map `dᵢ : P_{n+1} ⟶ Pₙ` of the standard polynomial resolution. -/
def standardFace (A : CommRingCat.{u}) (B : Under A) {n : ℕ} (i : Fin (n + 2)) :
    standardTerm A B (op ⦋n + 1⦌) ⟶ standardTerm A B (op ⦋n⦌) :=
  standardMap A B (SimplexCategory.δ i).op

/-- Unfolding of `standardFace` as `standardMap` of a coface. -/
theorem standardFace_eq (A : CommRingCat.{u}) (B : Under A) {n : ℕ} (i : Fin (n + 2)) :
    standardFace A B i = standardMap A B (SimplexCategory.δ i).op := rfl

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
  rfl

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
        ⟨faceSub A B x, faceSub_mem_ker A B x⟩ := rfl

/-- The scalar-extended conormal face difference is additive, satisfies the Leibniz
rule, and vanishes on the base ring. -/
theorem faceDifferenceDerivation_laws (A : CommRingCat.{u}) (B : Under A) :
    let d : (standardTerm A B (op ⦋1⦌)).right →
        (ModuleCat.restrictScalars (standardAugmentation A B (op ⦋1⦌)).hom).obj
          (naiveConormal A B B.right (selfHom A B)) :=
      fun x => (1 : B.right) ⊗ₜ[((functor A).obj B.right).right, (selfHom A B).right.hom]
        (faceSubCotangent A B x)
    (∀ x y, d (x + y) = d x + d y) ∧
      (∀ x y, d (x * y) = x • d y + y • d x) ∧
      (∀ a : A, d ((standardTerm A B (op ⦋1⦌)).hom a) = 0) := sorry

/-- The `A`-derivation into the scalar-extended conormal module sending `x` to
the conormal class of `d₀ x - d₁ x`. -/
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
    (faceDifferenceDerivation_laws A B).1
    (faceDifferenceDerivation_laws A B).2.1
    (faceDifferenceDerivation_laws A B).2.2

/-- The derivation `faceDifferenceDerivation` sends `x` to the class of `d₀ x - d₁ x`. -/
theorem faceDifferenceDerivation_apply (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right) :
    (faceDifferenceDerivation A B).d x =
      ((1 : B.right) ⊗ₜ[((functor A).obj B.right).right, (selfHom A B).right.hom]
        (faceSubCotangent A B x) :
        (ModuleCat.restrictScalars (standardAugmentation A B (op ⦋1⦌)).hom).obj
          (naiveConormal A B B.right (selfHom A B))) := rfl

/-- The degree-minus-one comparison from scalar-extended differentials to the
scalar-extended conormal module. -/
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
        (faceDifferenceDerivation A B).desc := rfl

/-- The generator formula: `toConormal` sends `d x` to the class of `d₀ x - d₁ x`. -/
theorem toConormal_tmul (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right) :
    ((ModuleCat.extendRestrictScalarsAdj
          (standardAugmentation A B (op ⦋1⦌)).hom).homEquiv _ _
        (toConormal A B))
        (CommRingCat.KaehlerDifferential.d x) =
      (faceDifferenceDerivation A B).d x := by
  rw [toConormal, Equiv.apply_symm_apply]
  exact ModuleCat.Derivation.desc_d (faceDifferenceDerivation A B) x

/-- On a pure tensor, the conormal comparison is the scalar multiple of the
conormal class of the difference of the first two faces. -/
theorem toConormal_tensor (A : CommRingCat.{u}) (B : Under A)
    (x : (standardTerm A B (op ⦋1⦌)).right) (b : B.right) :
    toConormal A B
        (b ⊗ₜ[(standardTerm A B (op ⦋1⦌)).right,
          (standardAugmentation A B (op ⦋1⦌)).hom] (CommRingCat.KaehlerDifferential.d x)) =
      HSMul.hSMul (α := B.right) (β := naiveConormal A B B.right (selfHom A B)) b
        ((1 : B.right) ⊗ₜ[((functor A).obj B.right).right, (selfHom A B).right.hom]
          (faceSubCotangent A B x)) := sorry

/-- The degree-zero self-presentation `P₀ ⟶ A[B]` used to identify Kähler differentials. -/
def selfToCounit (A : CommRingCat.{u}) (B : Under A) :
    standardTerm A B (op ⦋0⦌) ⟶ (functor A).obj B.right :=
  𝟙 _

/-- Unfolding of `selfToCounit` as the identity on `P₀ = A[B]`. -/
theorem selfToCounit_eq (A : CommRingCat.{u}) (B : Under A) :
    selfToCounit A B = 𝟙 _ := rfl

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
            (selfToCounit_comp_selfHom A B)).inv.app _) := rfl

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

/-- The face-difference comparison components commute with the differentials. -/
theorem toNaive_comm (A : CommRingCat.{u}) (B : Under A) :
    ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      toNaive_f A B i ≫ (selfNaiveComplex A B).d i j =
        (obj A B).d i j ≫ toNaive_f A B j := sorry

/-- The explicit cochain map `L_{B/A} ⟶ NL_{B/A}` of the standard resolution. -/
def toNaive (A : CommRingCat.{u}) (B : Under A) :
    obj A B ⟶ selfNaiveComplex A B where
  f := toNaive_f A B
  comm' := toNaive_comm A B

/-- Unfolding of the components of `toNaive`. -/
theorem toNaive_f_eq (A : CommRingCat.{u}) (B : Under A) (i : ℤ) :
    (toNaive A B).f i = toNaive_f A B i := rfl

/-- Degree `0` of `toNaive` is the identification of `Ω_{P₀/A} ⊗_{P₀} B`. -/
theorem toNaive_f_zero (A : CommRingCat.{u}) (B : Under A) :
    (toNaive A B).f 0 =
      (objXIso A B 0).hom ≫
        selfDifferentials A B ≫
        (naiveComplex_X_zero A B B.right (selfHom A B)).inv := rfl

/-- Degree `-1` of `toNaive` is the face-difference map `toConormal`. -/
theorem toNaive_f_negOne (A : CommRingCat.{u}) (B : Under A) :
    (toNaive A B).f (-1) =
      (objXIso A B 1).hom ≫
        toConormal A B ≫
        (naiveComplex_X_negOne A B B.right (selfHom A B)).inv := rfl

/-- The explicit comparison vanishes in every degree at most minus two. -/
theorem toNaive_f_negSucc_succ (A : CommRingCat.{u}) (B : Under A) (n : ℕ) :
    (toNaive A B).f (Int.negSucc (n + 1)) = 0 := rfl

/-- The explicit comparison vanishes in every positive degree. -/
theorem toNaive_f_pos (A : CommRingCat.{u}) (B : Under A) (n : ℕ) :
    (toNaive A B).f (Int.ofNat (n + 1)) = 0 := rfl

end CotangentComplex
end CategoryTheory.CommRingCat.Under

open CategoryTheory.CommRingCat.Under
open CategoryTheory.CommRingCat.Under.CotangentComplex
open DerivedCategory.TStructure

namespace Algebra.NaiveCotangent

/-- The comparison from the cotangent complex to the naive complex of the
canonical self-presentation, with the face-difference component in degree minus one. -/
abbrev toNaive (A : CommRingCat.{u}) (B : Under A) :
    obj A B ⟶ selfNaiveComplex A B :=
  CotangentComplex.toNaive A B

/-- The algebra-facing comparison is the explicit standard-resolution comparison. -/
theorem toNaive_eq (A : CommRingCat.{u}) (B : Under A) :
    toNaive A B = CotangentComplex.toNaive A B := rfl

/-- After truncation in degrees at least minus one, the explicit comparison agrees
with the inverse of the canonical derived comparison. -/
theorem toNaive_inv_toTruncGE_self (A : CommRingCat.{u}) (B : Under A) :
    (t.truncGE (-1)).map (DerivedCategory.Q.map (toNaive A B)) =
      inv (toTruncGE_self A B) ≫
        (t.truncGEπ (-1)).app (DerivedCategory.Q.obj (selfNaiveComplex A B)) :=
  sorry

end Algebra.NaiveCotangent
