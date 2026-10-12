/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import stacks_project.Chap85.Lemma_85_10_1_Fiberwise

/-!
# Čech cochain of an `O`-module on a fiberwise simplicial site

In Situation 85.3.3 case B, applying `Hom(-, M)` to the simplicial object
`n ↦ g_{n!} O_n` and its augmentation to `O` produces the canonical cochain
`0 → Hom(O, M) → Hom(g_{0!} O_0, M) → Hom(g_{1!} O_1, M) → ⋯`, equivalently
`0 → Γ(C_total, M) → Γ(C_0, M_0) → Γ(C_1, M_1) → ⋯`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex RingedSite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The cosimplicial abelian group `n ↦ Hom(g_{n!} O_n, M)` in case B. -/
def fiberModuleHomCosimplicial (M : SheafOfModules.{w} O) :
    CosimplicialObject AddCommGrpCat.{max u w} :=
  (fiberLowerShriekUnit F J O).rightOp ⋙ preadditiveYoneda.obj M

/-- Degree `n` of `fiberModuleHomCosimplicial` is `Hom(g_{n!} O_n, M)`. -/
theorem fiberModuleHomCosimplicial_obj (M : SheafOfModules.{w} O)
    (n : SimplexCategory) :
    (fiberModuleHomCosimplicial F J O M).obj n =
      (preadditiveYoneda.obj M).obj
        (op ((fiberModuleLowerShriek F J O n).obj (fiberComponentUnit F J O n))) :=
  sorry

/-- The unaugmented case B Čech cochain `Γ(C_•, M_•)` in nonnegative degrees. -/
abbrev fiberModuleCechComplex (M : SheafOfModules.{w} O) :
    CochainComplex AddCommGrpCat.{max u w} ℕ :=
  (alternatingCofaceMapComplex _).obj (fiberModuleHomCosimplicial F J O M)

/-- Degree `n` of `fiberModuleCechComplex` is `Hom(g_{n!} O_n, M)`. -/
theorem fiberModuleCechComplex_X (M : SheafOfModules.{w} O) (n : ℕ) :
    (fiberModuleCechComplex F J O M).X n =
      (fiberModuleHomCosimplicial F J O M).obj ⦋n⦌ :=
  sorry

/-- Differentials of `fiberModuleCechComplex` are the alternating sums of coface maps. -/
theorem fiberModuleCechComplex_d_eq (M : SheafOfModules.{w} O) (n : ℕ) :
    (fiberModuleCechComplex F J O M).d n (n + 1) =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) • (fiberModuleHomCosimplicial F J O M).δ i :=
  sorry

/-- The connecting map `Hom(O, M) ⟶ Hom(g_{0!} O_0, M)` induced by the case B
augmentation. -/
def fiberModuleCechConnect_d₀ (M : SheafOfModules.{w} O) :
    ((ChainComplex.single₀ _).obj
        ((preadditiveYoneda.obj M).obj (op (SheafOfModules.unit O)))).X 0 ⟶
      (fiberModuleCechComplex F J O M).X 0 :=
  (preadditiveYoneda.obj M).map (fiberModuleAugmented_hom_app F J O (op ⦋0⦌)).op

/-- `fiberModuleCechConnect_d₀` is `Hom` of the degree-zero case B augmentation. -/
theorem fiberModuleCechConnect_d₀_eq (M : SheafOfModules.{w} O) :
    fiberModuleCechConnect_d₀ F J O M =
      (preadditiveYoneda.obj M).map (fiberModuleAugmented_hom_app F J O (op ⦋0⦌)).op :=
  sorry

/-- The case B connecting map annihilates the outgoing differential of
`single₀ Hom(O, M)`. -/
theorem fiberModuleCechConnect_comp_d₀ (M : SheafOfModules.{w} O) :
    ((ChainComplex.single₀ _).obj
          ((preadditiveYoneda.obj M).obj (op (SheafOfModules.unit O)))).d 1 0 ≫
        fiberModuleCechConnect_d₀ F J O M = 0 :=
  sorry

/-- The case B connecting map annihilates the incoming differential of
`fiberModuleCechComplex`. -/
theorem fiberModuleCechConnect_d₀_comp (M : SheafOfModules.{w} O) :
    fiberModuleCechConnect_d₀ F J O M ≫ (fiberModuleCechComplex F J O M).d 0 1 = 0 :=
  sorry

/-- Connecting data for the case B ℤ-indexed Čech cochain, with `Hom(O, M)` in
degree `-1`. -/
def fiberModuleCechConnect (M : SheafOfModules.{w} O) :
    CochainComplex.ConnectData
      ((ChainComplex.single₀ _).obj
        ((preadditiveYoneda.obj M).obj (op (SheafOfModules.unit O))))
      (fiberModuleCechComplex F J O M) where
  d₀ := fiberModuleCechConnect_d₀ F J O M
  comp_d₀ := fiberModuleCechConnect_comp_d₀ F J O M
  d₀_comp := fiberModuleCechConnect_d₀_comp F J O M

/-- The canonical case B Čech cochain `0 → Hom(O, M) → Hom(g_{0!} O_0, M) → ⋯`. -/
def fiberModuleCechCochain (M : SheafOfModules.{w} O) :
    CochainComplex AddCommGrpCat.{max u w} ℤ :=
  (fiberModuleCechConnect F J O M).cochainComplex

/-- Degree `-1` of `fiberModuleCechCochain` is `Hom(O, M)`, equivalently
`Γ(C_total, M)`. -/
theorem fiberModuleCechCochain_X_negOne (M : SheafOfModules.{w} O) :
    (fiberModuleCechCochain F J O M).X (-1) =
      (preadditiveYoneda.obj M).obj (op (SheafOfModules.unit O)) :=
  sorry

/-- Degree `n ≥ 0` of `fiberModuleCechCochain` is `Hom(g_{n!} O_n, M)`. -/
theorem fiberModuleCechCochain_X_ofNat (M : SheafOfModules.{w} O) (n : ℕ) :
    (fiberModuleCechCochain F J O M).X n =
      (preadditiveYoneda.obj M).obj
        (op ((fiberModuleLowerShriek F J O ⦋n⦌).obj (fiberComponentUnit F J O ⦋n⦌))) :=
  sorry

/-- Adjunction identification `Hom(g_{n!} O_n, M) ≃ Hom(O_n, M_n)` in case B. -/
def fiberHomLowerShriekUnitEquiv (M : SheafOfModules.{w} O) (n : SimplexCategory) :
    ((fiberModuleLowerShriek F J O n).obj (fiberComponentUnit F J O n) ⟶ M) ≃
      (fiberComponentUnit F J O n ⟶
        (Cocontinuous.moduleInverseImage (ι F (op n)) O).obj M) :=
  (fiberModuleLowerShriek.adjunction F J O n).homEquiv _ _

/-- Combining the case B adjunction with `unitHomEquiv` yields `Γ(C_n, M_n)`. -/
def fiberHomLowerShriekUnitEquiv_sections (M : SheafOfModules.{w} O)
    (n : SimplexCategory) :
    ((fiberModuleLowerShriek F J O n).obj (fiberComponentUnit F J O n) ⟶ M) ≃
      ((Cocontinuous.moduleInverseImage (ι F (op n)) O).obj M :
          SheafOfModules.{w} (fiberComponentRingSheaf F J O n)).sections :=
  (fiberHomLowerShriekUnitEquiv F J O M n).trans
    ((Cocontinuous.moduleInverseImage (ι F (op n)) O).obj M :
        SheafOfModules.{w} (fiberComponentRingSheaf F J O n)).unitHomEquiv

end CategoryTheory.Grothendieck
