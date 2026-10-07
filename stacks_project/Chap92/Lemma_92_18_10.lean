module

public import stacks_project.Chap92.Lemma_92_18_10_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison of the sheaf cotangent complex with the naive cotangent complex

Lemma 92.18.10 records the canonical cochain map `L(φ) ⟶ NL(B/A)` identifying the naive
cotangent complex with the good truncation `τ_{≥ -1} L(φ)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open scoped SheafOfModules.RingedSite.CotangentComplex

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

/-- Lemma 92.18.10 (1). Let `C` be a site. Let `φ : A ⟶ B` be a homomorphism of sheaves of
rings on `C`. There is a canonical cochain map `L(φ) ⟶ NL_{B/A}` of the standard resolution
`P_•` of `B` over `A`, with `P₀ = A[B]` and `I = Ker(A[B] ⟶ B)`: the degree-`0` identification
of `Ω_{P₀/A} ⊗_{P₀} B`, the face-difference rule sending a local section `d f ⊗ b` to the class
of `(d₀ f - d₁ f) b` in `I/I²`, and `0` in degrees `≤ -2`. -/
@[stacks 08US]
def toNaive {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    L(φ) ⟶ NaiveCotangent.obj A (Under.mk φ) :=
  CotangentComplex.toNaive A (Under.mk φ)

/-- Lemma 92.18.10 (2). The canonical map identifies `NL_{B/A}` with the truncation
`τ_{≥ -1} L(φ)`. -/
@[stacks 08US]
instance toNaive_truncGE_quasiIso {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    QuasiIso (CochainComplex.truncGEMap (toNaive φ) (-1)) := sorry

/-- The naive cotangent complex is concentrated in degrees `≥ -1`, so `πTruncGE`
recovers `NL_{B/A}` from `τ_{≥ -1} NL_{B/A}`. -/
instance naiveObj_isGE_negOne {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (NaiveCotangent.obj A (Under.mk φ)).IsGE (-1) := sorry

/-- Degree `0` of the source-facing `toNaive` is the identification of
`Ω_{P₀/A} ⊗_{P₀} B`. -/
theorem toNaive_f_zero {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (toNaive φ).f 0 =
      (objXIso A (Under.mk φ) 0).hom ≫ selfDifferentials A (Under.mk φ) := sorry

/-- Degree `-1` of the source-facing `toNaive` is the face-difference map `toConormal`. -/
theorem toNaive_f_negOne {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    (toNaive φ).f (-1) =
      (objXIso A (Under.mk φ) 1).hom ≫ toConormal A (Under.mk φ) := sorry

end
end
