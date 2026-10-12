/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_13_4_Tower

/-!
# Lemma 85.13.4

In Situation 85.3.3, tensoring the Lemma 85.8.1 integer resolution with an
object `K` of `D(C_total)` produces a sequential Postnikov system for
`⋯ → X_2 → X_1 → X_0`, and `K` is the sequential homotopy colimit of `Y_n⟦n⟧`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.DerivedCategory
open HomologicalComplex
open scoped CategoryTheory.DerivedCategory.DerivedTensor

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
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasDerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [MonoidalCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [MonoidalPreadditive (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [∀ (K L : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf (topology C J) AddCommGrpCat.{w})) (ComplexShape.up ℤ)]
variable [@DerivedTensor.Right.Has (Sheaf (topology C J) AddCommGrpCat.{w}) _ _ _ _ _ _]
variable (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))

/-- Lemma 85.13.4 (1): in Situation 85.3.3 case A, the objects
`X_n = (g_{n!} ℤ) ⊗ᴸ K` and `Y_n = (g_{n!} ℤ → ⋯ → g_{0!} ℤ)⟦-n⟧ ⊗ᴸ K`, with the
canonical maps `Y_n ⟶ X_n` and `Y_n ⟶ Y_{n+1}⟦1⟧` of Lemma 85.8.1, form a
Postnikov system for `⋯ → X_2 → X_1 → X_0`. -/
@[stacks 0D9I]
abbrev abelianPostnikovTower :
    PostnikovSystem.Tower (DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :=
  IntegerPostnikov.tower C J K

/-- Term objects of `abelianPostnikovTower` are the source objects `X_n`. -/
theorem abelianPostnikovTower_X (n : ℕ) :
    (abelianPostnikovTower C J K).X n = IntegerPostnikov.X C J K n :=
  sorry

/-- Lemma 85.13.4 (2): in Situation 85.3.3 case A, `K` is the sequential homotopy
colimit of the objects `Y_n⟦n⟧` in `D(C_total)`, once the constant integer sheaf
is a derived left tensor unit for `K`. -/
@[stacks 0D9I]
theorem abelianPostnikov_isHocolim
    (h_unit : IntegerPostnikov.integerUnitTensor C J K ≅ K) :
    HomotopyColimit.IsOf (IntegerPostnikov.shiftedAux C J K) K :=
  sorry

end CategoryTheory.SimplicialSites

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
variable [MonoidalCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [MonoidalPreadditive (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [∀ (K L : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf (topology F J) AddCommGrpCat.{w})) (ComplexShape.up ℤ)]
variable [@DerivedTensor.Right.Has (Sheaf (topology F J) AddCommGrpCat.{w}) _ _ _ _ _ _]
variable (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))

/-- Lemma 85.13.4 (3): in Situation 85.3.3 case B, the objects
`X_n = (g_{n!} ℤ) ⊗ᴸ K` and `Y_n = (g_{n!} ℤ → ⋯ → g_{0!} ℤ)⟦-n⟧ ⊗ᴸ K`, with the
canonical maps `Y_n ⟶ X_n` and `Y_n ⟶ Y_{n+1}⟦1⟧` of Lemma 85.8.1, form a
Postnikov system for `⋯ → X_2 → X_1 → X_0`. -/
@[stacks 0D9I]
abbrev fiberAbelianPostnikovTower :
    PostnikovSystem.Tower (DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) :=
  IntegerPostnikov.tower F J K

/-- Term objects of `fiberAbelianPostnikovTower` are the source objects `X_n`. -/
theorem fiberAbelianPostnikovTower_X (n : ℕ) :
    (fiberAbelianPostnikovTower F J K).X n = IntegerPostnikov.X F J K n :=
  sorry

/-- Lemma 85.13.4 (4): in Situation 85.3.3 case B, `K` is the sequential homotopy
colimit of the objects `Y_n⟦n⟧` in `D(C_total)`, once the constant integer sheaf
is a derived left tensor unit for `K`. -/
@[stacks 0D9I]
theorem fiberAbelianPostnikov_isHocolim
    (h_unit : IntegerPostnikov.integerUnitTensor F J K ≅ K) :
    HomotopyColimit.IsOf (IntegerPostnikov.shiftedAux F J K) K :=
  sorry

end CategoryTheory.Grothendieck
