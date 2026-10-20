/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.CategoryTheory.Sites.Simplicial.IntegerResolution

/-!
# Hom cochain complex of `g_{n!} ℤ` on a morphism diagram of sites

Applying `Hom(-, F)` to the simplicial resolution
`n ↦ g_{n!} ℤ` yields a cosimplicial abelian group, an unaugmented cochain
complex, and the extended ℤ-indexed complex with `Hom(ℤ, F)` in degree `-1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The cosimplicial abelian group `n ↦ Hom(g_{n!} ℤ, F)` obtained by applying
`Hom(-, F)` to `lowerShriekConstant`. -/
def homCosimplicial (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    CosimplicialObject AddCommGrpCat.{max u w} :=
  (lowerShriekConstant C J).rightOp ⋙ preadditiveYoneda.obj F

/-- Degree `n` of `homCosimplicial` is the Hom group `Hom(g_{n!} ℤ, F)`. -/
theorem homCosimplicial_obj (F : Sheaf (topology C J) AddCommGrpCat.{w})
    (n : SimplexCategory) :
    (homCosimplicial C J F).obj n =
      (preadditiveYoneda.obj F).obj (op ((lowerShriekConstant C J).obj (op n))) :=
  sorry

/-- Functoriality of `n ↦ Hom(g_{n!} ℤ, F)` in the abelian sheaf `F`. -/
def homCosimplicialFunctor :
    Sheaf (topology C J) AddCommGrpCat.{w} ⥤
      CosimplicialObject AddCommGrpCat.{max u w} :=
  preadditiveYoneda ⋙
    (Functor.whiskeringLeft _ _ _).obj (lowerShriekConstant C J).rightOp

/-- The unaugmented cochain complex `Hom(g_{0!} ℤ, F) → Hom(g_{1!} ℤ, F) → ⋯`. -/
abbrev globalSectionsComplex (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    CochainComplex AddCommGrpCat.{max u w} ℕ :=
  (alternatingCofaceMapComplex _).obj (homCosimplicial C J F)

/-- Degree `n` of `globalSectionsComplex` is `Hom(g_{n!} ℤ, F)`. -/
theorem globalSectionsComplex_X (F : Sheaf (topology C J) AddCommGrpCat.{w}) (n : ℕ) :
    (globalSectionsComplex C J F).X n =
      (preadditiveYoneda.obj F).obj (op ((lowerShriekConstant C J).obj (op ⦋n⦌))) :=
  sorry

/-- Differentials of `globalSectionsComplex` are alternating sums of cofaces
`Hom(face i, F)`. -/
theorem globalSectionsComplex_d_eq (F : Sheaf (topology C J) AddCommGrpCat.{w}) (n : ℕ) :
    (globalSectionsComplex C J F).d n (n + 1) =
      ∑ i : Fin (n + 2),
        (-1 : ℤ) ^ (i : ℕ) • (preadditiveYoneda.obj F).map (face C J n i).op :=
  sorry

/-- The Hom group `Hom(ℤ, F)` of morphisms from the constant integer sheaf on
`C_total`. -/
def globalSectionsTotal (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    AddCommGrpCat.{max u w} :=
  (preadditiveYoneda.obj F).obj (op (constantIntegerSheaf (topology C J)))

/-- `globalSectionsTotal` is the preadditive Yoneda value at the constant sheaf `ℤ`. -/
theorem globalSectionsTotal_eq (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    globalSectionsTotal C J F =
      (preadditiveYoneda.obj F).obj (op (constantIntegerSheaf (topology C J))) :=
  sorry

/-- The Hom group `Hom(g_{n!} ℤ, F)` in degree `n`. -/
def globalSectionsStage (F : Sheaf (topology C J) AddCommGrpCat.{w})
    (n : SimplexCategory) : AddCommGrpCat.{max u w} :=
  (homCosimplicial C J F).obj n

/-- `globalSectionsStage` recovers the corresponding object of `homCosimplicial`. -/
theorem globalSectionsStage_eq (F : Sheaf (topology C J) AddCommGrpCat.{w})
    (n : SimplexCategory) :
    globalSectionsStage C J F n =
      (preadditiveYoneda.obj F).obj (op ((lowerShriekConstant C J).obj (op n))) :=
  sorry

/-- Adjunction identification `Hom(g_{n!} ℤ, F) ≃ Hom(ℤ_n, F_n)`. -/
def globalSectionsStage_addEquivRestrict (F : Sheaf (topology C J) AddCommGrpCat.{w})
    (n : SimplexCategory) :
    ((lowerShriekConstant C J).obj (op n) ⟶ F) ≃+
      (constantInteger C J n ⟶ (stageRestrict C J AddCommGrpCat.{w} n).obj F) where
  toEquiv := (abelianLowerShriek_adjunction C J n).homEquiv (constantInteger C J n) F
  map_add' := sorry

/-- The coaugmentation `Hom(ℤ, F) ⟶ Hom(g_{0!} ℤ, F)`, dual to the degree-zero
component of `augmentation`. -/
def globalSectionsCoaugmentation (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    globalSectionsTotal C J F ⟶ (globalSectionsComplex C J F).X 0 :=
  (preadditiveYoneda.obj F).map ((augmentation C J).f 0).op

/-- The coaugmentation is Hom of the simplicial augmentation at `⦋0⦌`. -/
theorem globalSectionsCoaugmentation_eq (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    globalSectionsCoaugmentation C J F =
      (preadditiveYoneda.obj F).map ((augmented C J).hom.app (op ⦋0⦌)).op :=
  sorry

/-- The coaugmentation equalizes the first coface differential. -/
theorem globalSectionsCoaugmentation_comp_d
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    globalSectionsCoaugmentation C J F ≫ (globalSectionsComplex C J F).d 0 1 = 0 :=
  sorry

/-- The connecting differential `Hom(ℤ, F) ⟶ Hom(g_{0!} ℤ, F)` from
`single₀ Hom(ℤ, F)` into the unaugmented Hom cochain. -/
def globalSectionsConnect_d₀ (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    ((ChainComplex.single₀ _).obj (globalSectionsTotal C J F)).X 0 ⟶
      (globalSectionsComplex C J F).X 0 :=
  globalSectionsCoaugmentation C J F

/-- The connecting differential is the coaugmentation `Hom(ℤ, F) ⟶ Hom(g_{0!} ℤ, F)`. -/
theorem globalSectionsConnect_d₀_eq (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    globalSectionsConnect_d₀ C J F = globalSectionsCoaugmentation C J F :=
  sorry

/-- The connecting differential annihilates the outgoing differential of
`single₀ Hom(ℤ, F)`. -/
theorem globalSectionsConnect_comp_d₀ (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    ((ChainComplex.single₀ _).obj (globalSectionsTotal C J F)).d 1 0 ≫
      globalSectionsConnect_d₀ C J F = 0 :=
  sorry

/-- The connecting differential equalizes the first coface of the unaugmented Hom cochain. -/
theorem globalSectionsConnect_d₀_comp (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    globalSectionsConnect_d₀ C J F ≫ (globalSectionsComplex C J F).d 0 1 = 0 :=
  sorry

/-- Connecting data for the ℤ-indexed Hom cochain, with `Hom(ℤ, F)` in degree `-1`. -/
def globalSectionsConnect (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    CochainComplex.ConnectData
      ((ChainComplex.single₀ _).obj (globalSectionsTotal C J F))
      (globalSectionsComplex C J F) where
  d₀ := globalSectionsConnect_d₀ C J F
  comp_d₀ := globalSectionsConnect_comp_d₀ C J F
  d₀_comp := globalSectionsConnect_d₀_comp C J F

/-- The extended cochain complex with `Hom(ℤ, F)` in degree `-1` and
`Hom(g_{n!} ℤ, F)` in degree `n`. -/
def globalSectionsExtended (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    CochainComplex AddCommGrpCat.{max u w} ℤ :=
  (globalSectionsConnect C J F).cochainComplex

/-- Degree `-1` of the extended complex is `Hom(ℤ, F)`, equivalently `Γ(C_total, F)`. -/
theorem globalSectionsExtended_X_negOne (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (globalSectionsExtended C J F).X (-1) = globalSectionsTotal C J F :=
  sorry

/-- Nonnegative degrees of the extended complex recover the unaugmented Hom complex. -/
theorem globalSectionsExtended_X_ofNat (F : Sheaf (topology C J) AddCommGrpCat.{w})
    (n : ℕ) :
    (globalSectionsExtended C J F).X n = (globalSectionsComplex C J F).X n :=
  sorry

/-- The differential out of degree `-1` is the coaugmentation. -/
theorem globalSectionsExtended_d_negOne_zero
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (globalSectionsExtended C J F).d (-1) 0 = globalSectionsConnect_d₀ C J F :=
  sorry

/-- The coaugmentation as a morphism from `Hom(ℤ, F)` concentrated in degree 0
to the unaugmented Hom complex. -/
def globalSectionsAugmentation (F : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (CochainComplex.single₀ _).obj (globalSectionsTotal C J F) ⟶
      globalSectionsComplex C J F :=
  (CochainComplex.fromSingle₀Equiv (globalSectionsComplex C J F)
      (globalSectionsTotal C J F)).symm
    ⟨globalSectionsCoaugmentation C J F, globalSectionsCoaugmentation_comp_d C J F⟩

/-- Functoriality of the unaugmented Hom cochain complex in the sheaf variable. -/
def globalSectionsComplexFunctor :
    Sheaf (topology C J) AddCommGrpCat.{w} ⥤
      CochainComplex AddCommGrpCat.{max u w} ℕ :=
  homCosimplicialFunctor C J ⋙ alternatingCofaceMapComplex _

/-- The augmented section complex on the total site is exact in degrees `-1` and `0`. -/
theorem globalSectionsExtended_exactAt_negOne_zero
    (F : Sheaf (topology C J) AddCommGrpCat.{w})
    (n : ℤ) (hn : n = (-1 : ℤ) ∨ n = (0 : ℤ)) :
    (globalSectionsExtended C J F).ExactAt n :=
  sorry

/-- The augmented section complex on the total site is acyclic for injective coefficients. -/
theorem globalSectionsExtended_acyclic_of_injective
    (F : Sheaf (topology C J) AddCommGrpCat.{w}) [Injective F] :
    (globalSectionsExtended C J F).Acyclic :=
  sorry

end CategoryTheory.SimplicialSites
