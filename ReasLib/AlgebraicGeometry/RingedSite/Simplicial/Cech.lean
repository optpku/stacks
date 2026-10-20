/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Čech cochain of an `O`-module on a morphism diagram of sites

Applying `Hom(-, F)` to the simplicial object
`n ↦ g_{n!} O_n` and its augmentation to `O` produces the canonical cochain
`0 → Hom(O, F) → Hom(g_{0!} O_0, F) → Hom(g_{1!} O_1, F) → ⋯`, equivalently
`0 → Γ(C_total, F) → Γ(C_0, F_0) → Γ(C_1, F_1) → ⋯`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex RingedSite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The cosimplicial abelian group `n ↦ Hom(g_{n!} O_n, F)`. -/
def moduleHomCosimplicial (F : SheafOfModules.{w} O) :
    CosimplicialObject AddCommGrpCat.{max u w} :=
  (lowerShriekUnit C J O).rightOp ⋙ preadditiveYoneda.obj F

/-- Degree `n` of `moduleHomCosimplicial` is `Hom(g_{n!} O_n, F)`. -/
theorem moduleHomCosimplicial_obj (F : SheafOfModules.{w} O) (n : SimplexCategory) :
    (moduleHomCosimplicial C J O F).obj n =
      (preadditiveYoneda.obj F).obj
        (op ((moduleLowerShriek C J O n).obj (componentUnit C J O n))) :=
  sorry

/-- The unaugmented Čech cochain `Γ(C_•, F_•)` in nonnegative degrees. -/
abbrev moduleCechComplex (F : SheafOfModules.{w} O) :
    CochainComplex AddCommGrpCat.{max u w} ℕ :=
  (alternatingCofaceMapComplex _).obj (moduleHomCosimplicial C J O F)

/-- Degree `n` of `moduleCechComplex` is `Hom(g_{n!} O_n, F)`. -/
theorem moduleCechComplex_X (F : SheafOfModules.{w} O) (n : ℕ) :
    (moduleCechComplex C J O F).X n = (moduleHomCosimplicial C J O F).obj ⦋n⦌ :=
  sorry

/-- Differentials of `moduleCechComplex` are the alternating sums of coface maps. -/
theorem moduleCechComplex_d_eq (F : SheafOfModules.{w} O) (n : ℕ) :
    (moduleCechComplex C J O F).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (moduleHomCosimplicial C J O F).δ i :=
  sorry

/-- The connecting map `Hom(O, F) ⟶ Hom(g_{0!} O_0, F)` induced by the augmentation. -/
def moduleCechConnect_d₀ (F : SheafOfModules.{w} O) :
    ((ChainComplex.single₀ _).obj
        ((preadditiveYoneda.obj F).obj (op (SheafOfModules.unit O)))).X 0 ⟶
      (moduleCechComplex C J O F).X 0 :=
  (preadditiveYoneda.obj F).map (moduleAugmented_hom_app C J O (op ⦋0⦌)).op

/-- `moduleCechConnect_d₀` is `Hom` of the degree-zero augmentation `g_{0!} O_0 ⟶ O`. -/
theorem moduleCechConnect_d₀_eq (F : SheafOfModules.{w} O) :
    moduleCechConnect_d₀ C J O F =
      (preadditiveYoneda.obj F).map (moduleAugmented_hom_app C J O (op ⦋0⦌)).op :=
  sorry

/-- The connecting map annihilates the outgoing differential of `single₀ Hom(O, F)`. -/
theorem moduleCechConnect_comp_d₀ (F : SheafOfModules.{w} O) :
    ((ChainComplex.single₀ _).obj
          ((preadditiveYoneda.obj F).obj (op (SheafOfModules.unit O)))).d 1 0 ≫
        moduleCechConnect_d₀ C J O F = 0 :=
  sorry

/-- The connecting map annihilates the incoming differential of `moduleCechComplex`. -/
theorem moduleCechConnect_d₀_comp (F : SheafOfModules.{w} O) :
    moduleCechConnect_d₀ C J O F ≫ (moduleCechComplex C J O F).d 0 1 = 0 :=
  sorry

/-- Connecting data for the ℤ-indexed Čech cochain, with `Hom(O, F)` in degree `-1`. -/
def moduleCechConnect (F : SheafOfModules.{w} O) :
    CochainComplex.ConnectData
      ((ChainComplex.single₀ _).obj
        ((preadditiveYoneda.obj F).obj (op (SheafOfModules.unit O))))
      (moduleCechComplex C J O F) where
  d₀ := moduleCechConnect_d₀ C J O F
  comp_d₀ := moduleCechConnect_comp_d₀ C J O F
  d₀_comp := moduleCechConnect_d₀_comp C J O F

/-- The canonical Čech cochain `0 → Hom(O, F) → Hom(g_{0!} O_0, F) → ⋯`. -/
def moduleCechCochain (F : SheafOfModules.{w} O) :
    CochainComplex AddCommGrpCat.{max u w} ℤ :=
  (moduleCechConnect C J O F).cochainComplex

/-- Degree `-1` of `moduleCechCochain` is `Hom(O, F)`, equivalently `Γ(C_total, F)`. -/
theorem moduleCechCochain_X_negOne (F : SheafOfModules.{w} O) :
    (moduleCechCochain C J O F).X (-1) =
      (preadditiveYoneda.obj F).obj (op (SheafOfModules.unit O)) :=
  sorry

/-- Degree `n ≥ 0` of `moduleCechCochain` is `Hom(g_{n!} O_n, F)`. -/
theorem moduleCechCochain_X_ofNat (F : SheafOfModules.{w} O) (n : ℕ) :
    (moduleCechCochain C J O F).X n =
      (preadditiveYoneda.obj F).obj
        (op ((moduleLowerShriek C J O ⦋n⦌).obj (componentUnit C J O ⦋n⦌))) :=
  sorry

/-- Adjunction identification `Hom(g_{n!} O_n, F) ≃ Hom(O_n, F_n)`. -/
def homLowerShriekUnitEquiv (F : SheafOfModules.{w} O) (n : SimplexCategory) :
    ((moduleLowerShriek C J O n).obj (componentUnit C J O n) ⟶ F) ≃
      (componentUnit C J O n ⟶
        (Cocontinuous.moduleInverseImage (ofStage C n) O).obj F) :=
  (moduleLowerShriek.adjunction C J O n).homEquiv _ _

/-- Combining the adjunction with `unitHomEquiv` yields `Γ(C_n, F_n)`. -/
def homLowerShriekUnitEquiv_sections (F : SheafOfModules.{w} O)
    (n : SimplexCategory) :
    ((moduleLowerShriek C J O n).obj (componentUnit C J O n) ⟶ F) ≃
      ((Cocontinuous.moduleInverseImage (ofStage C n) O).obj F :
          SheafOfModules.{w} (componentRingSheaf C J O n)).sections :=
  (homLowerShriekUnitEquiv C J O F n).trans
    ((Cocontinuous.moduleInverseImage (ofStage C n) O).obj F :
        SheafOfModules.{w} (componentRingSheaf C J O n)).unitHomEquiv

/-- The canonical augmented Čech cochain of a sheaf of modules is exact in degrees
`-1` and `0`. -/
theorem moduleCechCochain_exactAt_negOne_zero (F : SheafOfModules.{w} O) :
    (moduleCechCochain C J O F).ExactAt (-1) ∧
      (moduleCechCochain C J O F).ExactAt 0 :=
  sorry

/-- The canonical augmented Čech cochain of an injective sheaf of modules is acyclic. -/
theorem moduleCechCochain_acyclic_of_injective (F : SheafOfModules.{w} O)
    [Injective F] :
    (moduleCechCochain C J O F).Acyclic :=
  sorry

end CategoryTheory.SimplicialSites
