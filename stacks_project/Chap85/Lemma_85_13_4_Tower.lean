/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Derived.Postnikov
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Definition
public import stacks_project.Chap85.Lemma_85_8_1_Complex
public import stacks_project.Chap85.Lemma_85_8_1_Fiberwise

/-!
# Integer-resolution Postnikov towers on a simplicial site

In Situation 85.3.3, the alternating-face complex of `g_{n!} ℤ` is extended to a
cochain complex concentrated in degrees `≤ 0`. Tensoring its brutal Postnikov
tower with an object `K` of `D(C_total)` produces the sequential Postnikov
system of Lemma 85.13.4, in both the morphism-diagram and fiberwise presentations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CochainComplex CategoryTheory.MonoidalCategory
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
variable [MonoidalCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [MonoidalPreadditive (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [∀ (K L : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf (topology C J) AddCommGrpCat.{w})) (up ℤ)]
variable [@DerivedCategory.DerivedTensor.Right.Has
    (Sheaf (topology C J) AddCommGrpCat.{w}) _ _ _ _ _ _]

/-- The Lemma 85.8.1 complex `… → g_{2!} ℤ → g_{1!} ℤ → g_{0!} ℤ`, viewed as a
cochain complex of abelian sheaves on `C_total` concentrated in degrees `≤ 0`. -/
def integerCochain : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ :=
  (complex C J).extend embeddingDownNat

/-- Degree `-n` of `integerCochain` is the abelian sheaf `g_{n!} ℤ`. -/
def integerCochain_X (n : ℕ) :
    (integerCochain C J).X (Brutal.Tower.index n) ≅ (complex C J).X n :=
  (complex C J).extendXIso embeddingDownNat rfl

/-- Differentials of `integerCochain` are the alternating face sums of Lemma 85.8.1. -/
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

/-- `Y_n` is the derived tensor of the shifted brutal stage of `integerCochain` with `K`. -/
def Y_spec (n : ℕ) :
    Y C J K n ≅ Brutal.Derived.Postnikov.y (integerCochain C J) n ⊗ᴸ K :=
  Iso.refl _

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
  base := sorry
  distinguished := sorry
  comp := sorry

/-- Term objects of `tower` are the source objects `X_n`. -/
theorem tower_X (n : ℕ) : (tower C J K).X n = X C J K n :=
  sorry

/-- Auxiliary objects of `tower` are the source objects `Y_n`. -/
theorem tower_Y (n : ℕ) : (tower C J K).Y n = Y C J K n :=
  sorry

/-- The stored comparison `Y_n ⟶ X_n` is the canonical map `toX`. -/
theorem tower_toX (n : ℕ) : (tower C J K).toX n = toX C J K n :=
  sorry

/-- The finite Postnikov system of Definition 13.41.1 cut out from the sequential tower. -/
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
  sorry

/-- The derived object `(constantIntegerSheaf (topology C J))[0] ⊗ᴸ K`. -/
def integerUnitTensor :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) :=
  ((DerivedCategory.singleFunctor (Sheaf (topology C J) AddCommGrpCat.{w}) (0 : ℤ)).obj
      (constantIntegerSheaf (topology C J))) ⊗ᴸ K

/-- Unfolding `integerUnitTensor` recovers the derived tensor of the degree-zero
constant integer sheaf with `K`. -/
theorem integerUnitTensor_eq :
    integerUnitTensor C J K =
      ((DerivedCategory.singleFunctor (Sheaf (topology C J) AddCommGrpCat.{w}) (0 : ℤ)).obj
          (constantIntegerSheaf (topology C J))) ⊗ᴸ K :=
  sorry

/-- `K` is a sequential homotopy colimit of the objects `Y_n⟦n⟧` once the constant
integer sheaf is a derived left tensor unit for `K`. -/
theorem isHocolim (h_unit : integerUnitTensor C J K ≅ K) :
    HomotopyColimit.IsOf (shiftedAux C J K) K :=
  sorry

end CategoryTheory.SimplicialSites.IntegerPostnikov

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
variable [MonoidalCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [MonoidalPreadditive (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [∀ (K L : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf (topology F J) AddCommGrpCat.{w})) (up ℤ)]
variable [@DerivedCategory.DerivedTensor.Right.Has
    (Sheaf (topology F J) AddCommGrpCat.{w}) _ _ _ _ _ _]

/-- The Lemma 85.8.1 fiberwise complex `… → g_{2!} ℤ → g_{1!} ℤ → g_{0!} ℤ`, viewed as a
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

/-- `Y_n` is the derived tensor of the shifted brutal stage of `integerCochain` with `K`. -/
def Y_spec (n : ℕ) :
    Y F J K n ≅ Brutal.Derived.Postnikov.y (integerCochain F J) n ⊗ᴸ K :=
  Iso.refl _

/-- The sequential Postnikov tower of `⋯ → X_2 → X_1 → X_0` in the fiberwise presentation. -/
def tower : PostnikovSystem.Tower
    (DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) where
  X := X F J K
  d := d F J K
  Y := Y F J K
  toX := toX F J K
  toNext := toNext F J K
  connecting := connecting F J K
  base := sorry
  distinguished := sorry
  comp := sorry

/-- Term objects of the fiberwise `tower` are the source objects `X_n`. -/
theorem tower_X (n : ℕ) : (tower F J K).X n = X F J K n :=
  sorry

/-- Auxiliary objects of the fiberwise `tower` are the source objects `Y_n`. -/
theorem tower_Y (n : ℕ) : (tower F J K).Y n = Y F J K n :=
  sorry

/-- The stored comparison `Y_n ⟶ X_n` is the canonical fiberwise map `toX`. -/
theorem tower_toX (n : ℕ) : (tower F J K).toX n = toX F J K n :=
  sorry

/-- The finite Postnikov system of Definition 13.41.1 cut out from the fiberwise tower. -/
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
  sorry

/-- The derived object `(constantIntegerSheaf (topology F J))[0] ⊗ᴸ K`. -/
def integerUnitTensor :
    DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) :=
  ((DerivedCategory.singleFunctor (Sheaf (topology F J) AddCommGrpCat.{w}) (0 : ℤ)).obj
      (constantIntegerSheaf (topology F J))) ⊗ᴸ K

/-- Unfolding fiberwise `integerUnitTensor` recovers the derived tensor of the
degree-zero constant integer sheaf with `K`. -/
theorem integerUnitTensor_eq :
    integerUnitTensor F J K =
      ((DerivedCategory.singleFunctor (Sheaf (topology F J) AddCommGrpCat.{w}) (0 : ℤ)).obj
          (constantIntegerSheaf (topology F J))) ⊗ᴸ K :=
  sorry

/-- `K` is a sequential homotopy colimit of the fiberwise objects `Y_n⟦n⟧` once the
constant integer sheaf is a derived left tensor unit for `K`. -/
theorem isHocolim (h_unit : integerUnitTensor F J K ≅ K) :
    HomotopyColimit.IsOf (shiftedAux F J K) K :=
  sorry

end CategoryTheory.Grothendieck.IntegerPostnikov
