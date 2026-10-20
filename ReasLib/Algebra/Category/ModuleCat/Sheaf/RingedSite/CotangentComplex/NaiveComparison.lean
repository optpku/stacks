module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Homotopy
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cochain comparison from the sheaf cotangent complex to the naive cotangent complex

The standard resolution defines the canonical cochain map `L_{B/A} ⟶ NL_{B/A}` of a morphism of commutative
ring sheaves. Degree `0` is the identification of `Ω_{P₀/A} ⊗_{P₀} B` with the self-presentation
`A[B]`, degree `-1` is the face-difference map `Ω_{P₁/A} ⊗_{P₁} B ⟶ I/I²`, and the map
vanishes in degrees `≥ 1` and `≤ -2`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Opposite
open AlgebraicTopology
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open SheafOfModules.RingedSite.NaiveCotangent.Presentation
  renaming Hom → PresentationHom
open scoped Simplicial ZeroObject

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex

open CategoryTheory.Sheaf.FreeAlgebra

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

/-- The `i`-th face map `dᵢ : P_{n+1} ⟶ Pₙ` of the standard free-algebra resolution. -/
def standardFace (A : Sheaf J CommRingCat.{u}) (B : Under A) {n : ℕ} (i : Fin (n + 2)) :
    standardTerm A B (op ⦋n + 1⦌) ⟶ standardTerm A B (op ⦋n⦌) :=
  standardMap A B (SimplexCategory.δ i).op

/-- Unfolding of `standardFace` as `standardMap` of a coface. -/
theorem standardFace_eq (A : Sheaf J CommRingCat.{u}) (B : Under A)
    {n : ℕ} (i : Fin (n + 2)) :
    standardFace A B i = standardMap A B (SimplexCategory.δ i).op := sorry

/-- The two face maps `P₁ ⟶ P₀` are morphisms of algebras over `A`. -/
theorem face_baseSq (A : Sheaf J CommRingCat.{u}) (B : Under A) (i : Fin 2) :
    CommSq (𝟙 A) (standardTerm A B (op ⦋1⦌)).hom (standardTerm A B (op ⦋0⦌)).hom
      (standardFace A B i).right := sorry

/-- Each face map `P₁ ⟶ P₀` is compatible with the standard-resolution augmentations. -/
theorem face_targetSq (A : Sheaf J CommRingCat.{u}) (B : Under A) (i : Fin 2) :
    CommSq (standardFace A B i).right (standardAugmentation A B (op ⦋1⦌))
      (standardAugmentation A B (op ⦋0⦌)) (𝟙 B.right) := sorry

/-- The parallel pair of face maps `d₀, d₁ : P₁ ⟶ P₀` as a morphism of presentations. -/
def faceParallel (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    PresentationHom.Parallel (standardTerm A B (op ⦋1⦌)).hom
      (standardAugmentation A B (op ⦋1⦌)) (standardTerm A B (op ⦋0⦌)).hom
      (standardAugmentation A B (op ⦋0⦌)) where
  base := 𝟙 A
  first := (standardFace A B 0).right
  second := (standardFace A B 1).right
  target := 𝟙 B.right
  firstBaseSq := face_baseSq A B 0
  secondBaseSq := face_baseSq A B 1
  firstTargetSq := face_targetSq A B 0
  secondTargetSq := face_targetSq A B 1

/-- The first middle map of `faceParallel` is the face `d₀`. -/
theorem faceParallel_first (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (faceParallel A B).first = (standardFace A B 0).right := sorry

/-- The second middle map of `faceParallel` is the face `d₁`. -/
theorem faceParallel_second (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (faceParallel A B).second = (standardFace A B 1).right := sorry

/-- The canonical identification `P₀ ⟶ A[B]` of degree-zero standard-resolution terms. -/
def selfToCounit (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    standardTerm A B (op ⦋0⦌) ⟶ Presentation.obj A B :=
  𝟙 _

/-- Unfolding of `selfToCounit` as the identity on `P₀ = A[B]`. -/
theorem selfToCounit_eq (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    selfToCounit A B = 𝟙 _ := sorry

/-- Composing `selfToCounit` with the canonical presentation map recovers the degree-zero
augmentation. -/
theorem selfToCounit_comp_map (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (selfToCounit A B).right ≫ Presentation.map A B =
      standardAugmentation A B (op ⦋0⦌) := sorry

/-- The degree-zero self-presentation as a morphism of presentations `P₀ ⟶ A[B]`. -/
def selfPresentationHom (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    PresentationHom (standardTerm A B (op ⦋0⦌)).hom
      (standardAugmentation A B (op ⦋0⦌)) (Presentation.base A B) (Presentation.map A B) where
  base := 𝟙 A
  middle := (selfToCounit A B).right
  target := 𝟙 B.right
  baseSq := ⟨(Category.id_comp (Presentation.base A B)).trans (selfToCounit A B).w.symm⟩
  targetSq :=
    ⟨(selfToCounit_comp_map A B).trans
        (Category.comp_id (standardAugmentation A B (op ⦋0⦌))).symm⟩

/-- The middle map of `selfPresentationHom` is `selfToCounit`. -/
theorem selfPresentationHom_middle (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (selfPresentationHom A B).middle = (selfToCounit A B).right := sorry

/-- Degree-`0` identification `Ω_{P₀/A} ⊗_{P₀} B ⟶ Ω_{A[B]/A} ⊗_{A[B]} B`. -/
def selfDifferentials (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (simplicialModule A B).obj (op ⦋0⦌) ⟶
      conormalTensorTerm (Presentation.base A B) (Presentation.map A B) :=
  (extendIdIso B.right).inv.app ((simplicialModule A B).obj (op ⦋0⦌)) ≫
    PresentationHom.Differentials.map (selfPresentationHom A B)

/-- Unfolding of `selfDifferentials` as identity-extension followed by the presentation map. -/
theorem selfDifferentials_eq (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    selfDifferentials A B =
      (extendIdIso B.right).inv.app ((simplicialModule A B).obj (op ⦋0⦌)) ≫
        PresentationHom.Differentials.map (selfPresentationHom A B) := sorry

/-- The degree `-1` downward arrow `Ω_{P₁/A} ⊗_{P₁} B ⟶ I/I²`, sending a local section
`d f ⊗ b` to the class of `(d₀ f - d₁ f) b`. -/
def toConormal (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (simplicialModule A B).obj (op ⦋1⦌) ⟶
      conormalSource (Presentation.map A B) :=
  (extendIdIso B.right).inv.app ((simplicialModule A B).obj (op ⦋1⦌)) ≫
    PresentationHom.Parallel.differenceMap (faceParallel A B) ≫
      (extendIdIso B.right).inv.app
          (conormalSource (standardAugmentation A B (op ⦋0⦌))) ≫
        PresentationHom.Conormal.map (selfPresentationHom A B)

/-- Unfolding of `toConormal` as the face-difference map of `faceParallel`, transported to the
canonical presentation. -/
theorem toConormal_eq (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    toConormal A B =
      (extendIdIso B.right).inv.app ((simplicialModule A B).obj (op ⦋1⦌)) ≫
        PresentationHom.Parallel.differenceMap (faceParallel A B) ≫
          (extendIdIso B.right).inv.app
              (conormalSource (standardAugmentation A B (op ⦋0⦌))) ≫
            PresentationHom.Conormal.map (selfPresentationHom A B) := sorry

/-- Components of the explicit cochain map `L_{B/A} ⟶ NL_{B/A}`. -/
def toNaive_f (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    ∀ i : ℤ, (obj A B).X i ⟶ (NaiveCotangent.obj A B).X i
  | Int.ofNat 0 => (objXIso A B 0).hom ≫ selfDifferentials A B
  | Int.negSucc 0 => (objXIso A B 1).hom ≫ toConormal A B
  | Int.negSucc (_n + 1) => 0
  | Int.ofNat (_n + 1) => 0

/-- Degree `0` of `toNaive_f` is the identification of `Ω_{P₀/A} ⊗_{P₀} B`. -/
theorem toNaive_f_zero (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    toNaive_f A B 0 = (objXIso A B 0).hom ≫ selfDifferentials A B := sorry

/-- Degree `-1` of `toNaive_f` is the face-difference map `toConormal`. -/
theorem toNaive_f_negOne (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    toNaive_f A B (-1) = (objXIso A B 1).hom ≫ toConormal A B := sorry

/-- The explicit cochain map `L_{B/A} ⟶ NL_{B/A}` of the standard resolution. -/
def toNaive (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    obj A B ⟶ NaiveCotangent.obj A B where
  f := toNaive_f A B
  comm' := sorry

/-- Unfolding of the components of `toNaive`. -/
theorem toNaive_f_eq (A : Sheaf J CommRingCat.{u}) (B : Under A) (i : ℤ) :
    (toNaive A B).f i = toNaive_f A B i := sorry

/-- Degree `0` of `toNaive` is the identification of `Ω_{P₀/A} ⊗_{P₀} B`. -/
theorem toNaive_zero (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (toNaive A B).f 0 = (objXIso A B 0).hom ≫ selfDifferentials A B := sorry

/-- Degree `-1` of `toNaive` is the face-difference map `toConormal`. -/
theorem toNaive_negOne (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (toNaive A B).f (-1) = (objXIso A B 1).hom ≫ toConormal A B := sorry

/-- After `τ_{≥ -1}`, the comparison `toNaive` is a quasi-isomorphism, identifying
`NL_{B/A}` with `τ_{≥ -1} L_{B/A}`. -/
theorem toNaive_truncGE_quasiIso (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    QuasiIso (CochainComplex.truncGEMap (toNaive A B) (-1)) := sorry

/-- The comparison `toNaive` is a quasi-isomorphism in cohomological degree `0`. -/
theorem toNaive_quasiIsoAt_zero (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    QuasiIsoAt (toNaive A B) 0 := sorry

/-- The comparison `toNaive` is a quasi-isomorphism in cohomological degree `-1`. -/
theorem toNaive_quasiIsoAt_negOne (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    QuasiIsoAt (toNaive A B) (-1) := sorry

/-- The comparison `toNaive` is a quasi-isomorphism in every cohomological degree `≥ -1`. -/
theorem toNaive_quasiIsoAt_ge (A : Sheaf J CommRingCat.{u}) (B : Under A)
    {n : ℤ} (hn : -1 ≤ n) : QuasiIsoAt (toNaive A B) n := sorry

/-- The naive cotangent complex is concentrated in degrees `≥ -1`. -/
theorem naiveObj_isGE_negOne (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (NaiveCotangent.obj A B).IsGE (-1) := sorry

/-- The naive cotangent complex is concentrated in degrees `≤ 0`. -/
theorem naiveObj_isLE_zero (A : Sheaf J CommRingCat.{u}) (B : Under A) :
    (NaiveCotangent.obj A B).IsLE 0 := sorry

attribute [instance] toNaive_truncGE_quasiIso naiveObj_isGE_negOne

end SheafOfModules.RingedSite.CotangentComplex
