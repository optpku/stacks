/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Derived.Postnikov
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Definition
public import ReasLib.CategoryTheory.Sites.AbelianTensor
public import ReasLib.CategoryTheory.Sites.Simplicial.IntegerResolution

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CochainComplex CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open HomologicalComplex ComplexShape
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites.IntegerPostnikov

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
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasDerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [∀ (K L : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf (topology C J) AddCommGrpCat.{w})) (up ℤ)]
variable [DerivedCategory.DerivedTensor.Right.Has (C := (Sheaf (topology C J) AddCommGrpCat.{w}))]

/-- The alternating-face resolution `… → g_{2!} ℤ → g_{1!} ℤ → g_{0!} ℤ`, viewed as a
cochain complex of abelian sheaves on `C_total` concentrated in degrees `≤ 0`. -/
def integerCochain : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ :=
  (complex C J).extend embeddingDownNat

/-- Degree `-n` of `integerCochain` is the abelian sheaf `g_{n!} ℤ`. -/
def integerCochain_X (n : ℕ) :
    (integerCochain C J).X (Brutal.Tower.index n) ≅ (complex C J).X n :=
  (complex C J).extendXIso embeddingDownNat rfl

/-- Differentials of `integerCochain` are the alternating face sums. -/
theorem integerCochain_d (n : ℕ) :
    (integerCochain C J).d (Brutal.Tower.index (n + 1)) (Brutal.Tower.index n) =
      (integerCochain_X C J (n + 1)).hom ≫ (complex C J).d (n + 1) n ≫
        (integerCochain_X C J n).inv :=
  sorry

variable (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))

/-- The object `X_n = (g_{n!} ℤ) ⊗ᴸ K` of `D(C_total)`. -/
def X (n : ℕ) : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) :=
  (DerivedCategory.DerivedTensor.Right.functor K).obj
    (Brutal.Derived.Postnikov.x (integerCochain C J) n)

/-- The object `Y_n = (g_{n!} ℤ → ⋯ → g_{0!} ℤ)⟦-n⟧ ⊗ᴸ K` of `D(C_total)`. -/
def Y (n : ℕ) : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) :=
  (DerivedCategory.DerivedTensor.Right.functor K).obj
    (Brutal.Derived.Postnikov.y (integerCochain C J) n)

/-- The differential `X_{n+1} ⟶ X_n` induced by the alternating face sum. -/
def d (n : ℕ) : X C J K (n + 1) ⟶ X C J K n :=
  (DerivedCategory.DerivedTensor.Right.functor K).map
    (Brutal.Derived.Postnikov.d (integerCochain C J) n)

/-- The canonical comparison `Y_n ⟶ X_n`. -/
def toX (n : ℕ) : Y C J K n ⟶ X C J K n :=
  (DerivedCategory.DerivedTensor.Right.functor K).map
    (Brutal.Derived.Postnikov.toX (integerCochain C J) n)

/-- The second map `X_{n+1} ⟶ Y_n` of a stage triangle. -/
def toNext (n : ℕ) : X C J K (n + 1) ⟶ Y C J K n :=
  (DerivedCategory.DerivedTensor.Right.functor K).map
    (Brutal.Derived.Postnikov.toNext (integerCochain C J) n)

/-- The connecting map `Y_n ⟶ Y_{n+1}⟦1⟧`, reassociated along derived tensor. -/
def connecting (n : ℕ) : Y C J K n ⟶ (Y C J K (n + 1))⟦(1 : ℤ)⟧ :=
  (DerivedCategory.DerivedTensor.Right.functor K).map
      (Brutal.Derived.Postnikov.connecting (integerCochain C J) n) ≫
    ((DerivedCategory.DerivedTensor.Right.functor K).commShiftIso (1 : ℤ)).hom.app
      (Brutal.Derived.Postnikov.y (integerCochain C J) (n + 1))

/-- `X_n` is the derived tensor of the degree-zero sheaf `g_{n!} ℤ` with `K`. -/
def X_spec (n : ℕ) :
    X C J K n ≅
      ((DerivedCategory.singleFunctor (Sheaf (topology C J) AddCommGrpCat.{w}) (0 : ℤ)).obj
          ((complex C J).X n)) ⊗ᴸ K :=
  (DerivedCategory.DerivedTensor.Right.functor K).mapIso
    ((DerivedCategory.singleFunctor (Sheaf (topology C J) AddCommGrpCat.{w}) (0 : ℤ)).mapIso
      (integerCochain_X C J n))

/-- The comparison from the zeroth stage to the zeroth term is invertible. -/
instance base : IsIso (toX C J K 0) :=
  sorry

/-- Consecutive stages and their canonical maps form distinguished triangles. -/
theorem distinguished (n : ℕ) :
    Triangle.mk (toX C J K (n + 1)) (toNext C J K n) (connecting C J K n) ∈
      distTriang (DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :=
  sorry

/-- Factoring through the preceding stage recovers the row differential. -/
theorem comp (n : ℕ) : toNext C J K n ≫ toX C J K n = d C J K n :=
  sorry

/-- The sequential Postnikov tower of `⋯ → X_2 → X_1 → X_0` obtained by tensoring
the brutal tower of `integerCochain` with `K`. -/
def tower : PostnikovSystem.Tower
    (DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) where
  X := X C J K
  d := d C J K
  Y := Y C J K
  toX := toX C J K
  toNext := toNext C J K
  connecting := connecting C J K
  base := base C J K
  distinguished := distinguished C J K
  comp := comp C J K

/-- The term objects of the tower are the derived tensor terms `X_n`. -/
theorem tower_X (n : ℕ) : (tower C J K).X n = X C J K n :=
  rfl

/-- The auxiliary objects of the tower are the derived tensor stages `Y_n`. -/
theorem tower_Y (n : ℕ) : (tower C J K).Y n = Y C J K n :=
  rfl

/-- The stored comparison `Y_n ⟶ X_n` is the canonical map `toX`. -/
theorem tower_toX (n : ℕ) : (tower C J K).toX n = toX C J K n :=
  rfl

/-- The finite Postnikov system cut out from the sequential tower. -/
def finite (n : ℕ) : PostnikovSystem ((tower C J K).row n) :=
  (tower C J K).finite n

/-- The successive map `Y_n⟦n⟧ ⟶ Y_{n+1}⟦n+1⟧` induced by the Postnikov connecting map. -/
def shiftedAuxMap (n : ℕ) :
    (Y C J K n)⟦(n : ℤ)⟧ ⟶ (Y C J K (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧ :=
  (connecting C J K n)⟦(n : ℤ)⟧' ≫
    (shiftFunctorAdd' _ (1 : ℤ) (n : ℤ) ((n + 1 : ℕ) : ℤ)
        ((add_comm (1 : ℤ) n).trans (Nat.cast_succ n).symm)).inv.app (Y C J K (n + 1))

/-- The sequential diagram `n ↦ Y_n⟦n⟧` whose homotopy colimit is `K`. -/
def shiftedAux : ℕ ⥤ DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) :=
  Functor.ofSequence (shiftedAuxMap C J K)

/-- Evaluating `shiftedAux` at `n` recovers `Y_n⟦n⟧`. -/
theorem shiftedAux_obj (n : ℕ) :
    (shiftedAux C J K).obj n = (Y C J K n)⟦(n : ℤ)⟧ :=
  rfl

end CategoryTheory.SimplicialSites.IntegerPostnikov

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
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasDerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [∀ (K L : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf (topology C J) AddCommGrpCat.{w})) (up ℤ)]
variable [DerivedCategory.DerivedTensor.Right.Has (C := (Sheaf (topology C J) AddCommGrpCat.{w}))]

variable (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))

/-- Every derived abelian sheaf is a homotopy colimit of the shifted stages of its
integer-resolution tensor Postnikov tower. -/
theorem abelianPostnikov_isHocolim :
    HomotopyColimit.IsOf (IntegerPostnikov.shiftedAux C J K) K :=
  sorry

end CategoryTheory.SimplicialSites
