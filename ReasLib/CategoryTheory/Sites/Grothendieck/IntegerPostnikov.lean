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
public import ReasLib.CategoryTheory.Sites.Grothendieck.IntegerResolution

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CochainComplex CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open HomologicalComplex ComplexShape
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck.IntegerPostnikov

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (F.obj n)ᵒᵖ ⥤ Type w, (ι F n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasDerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [∀ (K L : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf (topology F J) AddCommGrpCat.{w})) (up ℤ)]
variable [DerivedCategory.DerivedTensor.Right.Has (C := (Sheaf (topology F J) AddCommGrpCat.{w}))]

/-- The fiberwise alternating-face resolution `… → g_{2!} ℤ → g_{1!} ℤ → g_{0!} ℤ`, viewed as a
cochain complex of abelian sheaves on `C_total` concentrated in degrees `≤ 0`. -/
def integerCochain : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ :=
  (fiberComplex F J).extend embeddingDownNat

/-- Degree `-n` of the fiberwise `integerCochain` is the abelian sheaf `g_{n!} ℤ`. -/
def integerCochain_X (n : ℕ) :
    (integerCochain F J).X (Brutal.Tower.index n) ≅ (fiberComplex F J).X n :=
  (fiberComplex F J).extendXIso embeddingDownNat rfl

/-- Differentials of the fiberwise `integerCochain` are the alternating face sums. -/
theorem integerCochain_d (n : ℕ) :
    (integerCochain F J).d (Brutal.Tower.index (n + 1)) (Brutal.Tower.index n) =
      (integerCochain_X F J (n + 1)).hom ≫ (fiberComplex F J).d (n + 1) n ≫
        (integerCochain_X F J n).inv :=
  sorry

variable (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))

/-- The object `X_n = (g_{n!} ℤ) ⊗ᴸ K` of `D(C_total)` in the fiberwise presentation. -/
def X (n : ℕ) : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) :=
  (DerivedCategory.DerivedTensor.Right.functor K).obj
    (Brutal.Derived.Postnikov.x (integerCochain F J) n)

/-- The object `Y_n = (g_{n!} ℤ → ⋯ → g_{0!} ℤ)⟦-n⟧ ⊗ᴸ K` in the fiberwise presentation. -/
def Y (n : ℕ) : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) :=
  (DerivedCategory.DerivedTensor.Right.functor K).obj
    (Brutal.Derived.Postnikov.y (integerCochain F J) n)

/-- The differential `X_{n+1} ⟶ X_n` induced by the fiberwise alternating face sum. -/
def d (n : ℕ) : X F J K (n + 1) ⟶ X F J K n :=
  (DerivedCategory.DerivedTensor.Right.functor K).map
    (Brutal.Derived.Postnikov.d (integerCochain F J) n)

/-- The canonical comparison `Y_n ⟶ X_n` in the fiberwise presentation. -/
def toX (n : ℕ) : Y F J K n ⟶ X F J K n :=
  (DerivedCategory.DerivedTensor.Right.functor K).map
    (Brutal.Derived.Postnikov.toX (integerCochain F J) n)

/-- The second map `X_{n+1} ⟶ Y_n` of a fiberwise stage triangle. -/
def toNext (n : ℕ) : X F J K (n + 1) ⟶ Y F J K n :=
  (DerivedCategory.DerivedTensor.Right.functor K).map
    (Brutal.Derived.Postnikov.toNext (integerCochain F J) n)

/-- The connecting map `Y_n ⟶ Y_{n+1}⟦1⟧` in the fiberwise presentation. -/
def connecting (n : ℕ) : Y F J K n ⟶ (Y F J K (n + 1))⟦(1 : ℤ)⟧ :=
  (DerivedCategory.DerivedTensor.Right.functor K).map
      (Brutal.Derived.Postnikov.connecting (integerCochain F J) n) ≫
    ((DerivedCategory.DerivedTensor.Right.functor K).commShiftIso (1 : ℤ)).hom.app
      (Brutal.Derived.Postnikov.y (integerCochain F J) (n + 1))

/-- `X_n` is the derived tensor of the degree-zero sheaf `g_{n!} ℤ` with `K`. -/
def X_spec (n : ℕ) :
    X F J K n ≅
      ((DerivedCategory.singleFunctor (Sheaf (topology F J) AddCommGrpCat.{w}) (0 : ℤ)).obj
          ((fiberComplex F J).X n)) ⊗ᴸ K :=
  (DerivedCategory.DerivedTensor.Right.functor K).mapIso
    ((DerivedCategory.singleFunctor (Sheaf (topology F J) AddCommGrpCat.{w}) (0 : ℤ)).mapIso
      (integerCochain_X F J n))

/-- The comparison from the zeroth stage to the zeroth term is invertible. -/
instance base : IsIso (toX F J K 0) :=
  sorry

/-- Consecutive stages and their canonical maps form distinguished triangles. -/
theorem distinguished (n : ℕ) :
    Triangle.mk (toX F J K (n + 1)) (toNext F J K n) (connecting F J K n) ∈
      distTriang (DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) :=
  sorry

/-- Factoring through the preceding stage recovers the row differential. -/
theorem comp (n : ℕ) : toNext F J K n ≫ toX F J K n = d F J K n :=
  sorry

/-- The sequential Postnikov tower of `⋯ → X_2 → X_1 → X_0` in the fiberwise presentation. -/
def tower : PostnikovSystem.Tower
    (DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) where
  X := X F J K
  d := d F J K
  Y := Y F J K
  toX := toX F J K
  toNext := toNext F J K
  connecting := connecting F J K
  base := base F J K
  distinguished := distinguished F J K
  comp := comp F J K

/-- The term objects of the fiberwise tower are the derived tensor terms `X_n`. -/
theorem tower_X (n : ℕ) : (tower F J K).X n = X F J K n :=
  rfl

/-- The auxiliary objects of the fiberwise tower are the derived tensor stages `Y_n`. -/
theorem tower_Y (n : ℕ) : (tower F J K).Y n = Y F J K n :=
  rfl

/-- The stored comparison `Y_n ⟶ X_n` is the canonical fiberwise map `toX`. -/
theorem tower_toX (n : ℕ) : (tower F J K).toX n = toX F J K n :=
  rfl

/-- The finite Postnikov system cut out from the fiberwise tower. -/
def finite (n : ℕ) : PostnikovSystem ((tower F J K).row n) :=
  (tower F J K).finite n

/-- The successive map `Y_n⟦n⟧ ⟶ Y_{n+1}⟦n+1⟧` in the fiberwise presentation. -/
def shiftedAuxMap (n : ℕ) :
    (Y F J K n)⟦(n : ℤ)⟧ ⟶ (Y F J K (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧ :=
  (connecting F J K n)⟦(n : ℤ)⟧' ≫
    (shiftFunctorAdd' _ (1 : ℤ) (n : ℤ) ((n + 1 : ℕ) : ℤ)
        ((add_comm (1 : ℤ) n).trans (Nat.cast_succ n).symm)).inv.app (Y F J K (n + 1))

/-- The sequential diagram `n ↦ Y_n⟦n⟧` in the fiberwise presentation. -/
def shiftedAux : ℕ ⥤ DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) :=
  Functor.ofSequence (shiftedAuxMap F J K)

/-- Evaluating the fiberwise `shiftedAux` at `n` recovers `Y_n⟦n⟧`. -/
theorem shiftedAux_obj (n : ℕ) :
    (shiftedAux F J K).obj n = (Y F J K n)⟦(n : ℤ)⟧ :=
  rfl

end CategoryTheory.Grothendieck.IntegerPostnikov

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (F.obj n)ᵒᵖ ⥤ Type w, (ι F n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasDerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [∀ (K L : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf (topology F J) AddCommGrpCat.{w})) (up ℤ)]
variable [DerivedCategory.DerivedTensor.Right.Has (C := (Sheaf (topology F J) AddCommGrpCat.{w}))]

variable (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))

/-- Every derived abelian sheaf is a homotopy colimit of the shifted stages of its
integer-resolution tensor Postnikov tower. -/
theorem fiberAbelianPostnikov_isHocolim :
    HomotopyColimit.IsOf (IntegerPostnikov.shiftedAux F J K) K :=
  sorry

end CategoryTheory.Grothendieck
