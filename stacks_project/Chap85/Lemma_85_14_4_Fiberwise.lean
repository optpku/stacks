/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Derived.Postnikov
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Definition
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Basic
public import stacks_project.Chap85.Lemma_85_10_1_Fiberwise

/-!
# Sequential Postnikov tower of `g_{n!} O_n` tensored with an object of `D(O)`, case B

In Situation 85.3.3 case B, embed the alternating-face resolution
`… → g_{2!} O_2 → g_{1!} O_1 → g_{0!} O_0` as a cochain complex concentrated in
degrees `≤ 0`, form its brutal derived Postnikov tower, and apply
`- ⊗^L K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory
open ComplexShape DerivedCategory HomologicalComplex
open CochainComplex.Brutal.Derived.Postnikov

noncomputable section

universe u v w uA vA wA

namespace CategoryTheory.Grothendieck

/-- Explicit-parameter form of `DerivedTensor.Right.Has`. -/
abbrev HasRightDerivedTensor (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [∀ (K L : CochainComplex A ℤ),
      HomologicalComplex.HasMapBifunctor K L (curriedTensor A) (up ℤ)] : Prop :=
  @DerivedTensor.Right.Has A inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance

/-- `HasRightDerivedTensor A` is `DerivedTensor.Right.Has` on the same category. -/
theorem hasRightDerivedTensor_iff {A : Type uA} [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [∀ (K L : CochainComplex A ℤ),
      HomologicalComplex.HasMapBifunctor K L (curriedTensor A) (up ℤ)] :
    HasRightDerivedTensor A ↔
      @DerivedTensor.Right.Has A inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance :=
  sorry

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) CommRingCat.{w})
variable [(topology F J).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose
    (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (Opposite.op n))ᵒᵖ ⥤ Type w,
    (ι F (Opposite.op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (Opposite.op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J (Sheaf.ringSheafOfComm O) n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J (Sheaf.ringSheafOfComm O) φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The underlying ring sheaf of a commutative ring sheaf on the total fiberwise site. -/
abbrev fiberTotalRingSheaf : Sheaf (topology F J) RingCat.{w} :=
  Sheaf.ringSheafOfComm O

/-- Unfolding `fiberTotalRingSheaf` recovers `Sheaf.ringSheafOfComm`. -/
theorem fiberTotalRingSheaf_eq : fiberTotalRingSheaf F J O = Sheaf.ringSheafOfComm O :=
  sorry

/-- Sheaves of modules over the underlying ring sheaf of `O` on the total fiberwise site. -/
abbrev fiberTotalModules :=
  SheafOfModules.{w} (fiberTotalRingSheaf F J O)

/-- Unfolding `fiberTotalModules` recovers sheaves of modules over `Sheaf.ringSheafOfComm O`. -/
theorem fiberTotalModules_eq :
    fiberTotalModules F J O = SheafOfModules.{w} (Sheaf.ringSheafOfComm O) :=
  sorry

/-- The cochain complex obtained by embedding
`… → g_{2!} O_2 → g_{1!} O_1 → g_{0!} O_0` along `n ↦ -n`. -/
def fiberModuleCochain : CochainComplex (fiberTotalModules F J O) ℤ :=
  (fiberModuleComplex F J (fiberTotalRingSheaf F J O)).extend embeddingDownNat

/-- The embedded resolution is concentrated in cohomological degrees `≤ 0`. -/
instance fiberModuleCochain_isStrictlyLE : (fiberModuleCochain F J O).IsStrictlyLE 0 :=
  sorry

/-- Degree `-n` of `fiberModuleCochain` is the sheaf of modules `g_{n!} O_n`. -/
def fiberModuleCochain_XIso (n : ℕ) :
    (fiberModuleCochain F J O).X (CochainComplex.Brutal.Tower.index n) ≅
      (fiberModuleComplex F J (fiberTotalRingSheaf F J O)).X n :=
  (fiberModuleComplex F J (fiberTotalRingSheaf F J O)).extendXIso embeddingDownNat rfl

variable [UnivLE.{max u v, w}]

/-- Canonical derived-category structure on modules over the commutative ring sheaf `O`. -/
noncomputable instance fiberTotalModules_hasDerivedCategory :
    HasDerivedCategory (fiberTotalModules F J O) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} (topology F J) O)

/-- The derived category `D(O)` of modules on the total fiberwise site. -/
abbrev fiberTotalDerived :=
  RingedSite.Hom.ModuleDerived.{w}
    (RingedSite.ofCommRingSheaf.{u, v, w} (topology F J) O)

/-- Unfolding `fiberTotalDerived` recovers `DerivedCategory` of `fiberTotalModules`. -/
theorem fiberTotalDerived_eq : fiberTotalDerived F J O = DerivedCategory (fiberTotalModules F J O) :=
  sorry

/-- Canonical tensor product on modules over the commutative ring sheaf `O`. -/
noncomputable instance fiberTotalModules_monoidalCategory :
    MonoidalCategory (fiberTotalModules F J O) :=
  SheafOfModules.RingedSite.moduleMonoidalCategory O

/-- The tensor product of `O`-modules is additive in both variables. -/
instance fiberTotalModules_monoidalPreadditive :
    MonoidalPreadditive (fiberTotalModules F J O) :=
  SheafOfModules.RingedSite.monoidalPreadditive

/-- Unbounded cochain tensor totalization exists for modules over `O`. -/
instance fiberTotalModules_hasMapBifunctor
    (X Y : CochainComplex (fiberTotalModules F J O) ℤ) :
    HomologicalComplex.HasMapBifunctor X Y
      (curriedTensor (fiberTotalModules F J O)) (up ℤ) :=
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor O X Y

variable [HasRightDerivedTensor (fiberTotalModules F J O)]

/-- The canonical sequential Postnikov tower of the embedded resolution, before
tensoring with an object of `D(O)`. -/
def fiberModuleUnitPostnikovTower : PostnikovSystem.Tower (fiberTotalDerived F J O) :=
  tower (fiberModuleCochain F J O)

/-- The unit tower is the brutal derived Postnikov tower of `fiberModuleCochain`. -/
theorem fiberModuleUnitPostnikovTower_eq :
    fiberModuleUnitPostnikovTower F J O = tower (fiberModuleCochain F J O) :=
  sorry

variable (K : fiberTotalDerived F J O)

/-- The term `X_n = (g_{n!} O_n) ⊗^L_O K` in `D(O)`. -/
def fiberModulePostnikovX (n : ℕ) : fiberTotalDerived F J O :=
  (DerivedTensor.Right.functor K).obj (x (fiberModuleCochain F J O) n)

/-- The auxiliary object
`Y_n = (g_{n!} O_n → ⋯ → g_{0!} O_0)[-n] ⊗^L_O K` in `D(O)`. -/
def fiberModulePostnikovY (n : ℕ) : fiberTotalDerived F J O :=
  (DerivedTensor.Right.functor K).obj (y (fiberModuleCochain F J O) n)

/-- The differential `X_{n+1} ⟶ X_n` induced by the alternating-face maps. -/
def fiberModulePostnikov_d (n : ℕ) :
    fiberModulePostnikovX F J O K (n + 1) ⟶ fiberModulePostnikovX F J O K n :=
  (DerivedTensor.Right.functor K).map (d (fiberModuleCochain F J O) n)

/-- The canonical comparison `Y_n ⟶ X_n`. -/
def fiberModulePostnikov_toX (n : ℕ) :
    fiberModulePostnikovY F J O K n ⟶ fiberModulePostnikovX F J O K n :=
  (DerivedTensor.Right.functor K).map (toX (fiberModuleCochain F J O) n)

/-- The second map `X_{n+1} ⟶ Y_n` of a stage triangle. -/
def fiberModulePostnikov_toNext (n : ℕ) :
    fiberModulePostnikovX F J O K (n + 1) ⟶ fiberModulePostnikovY F J O K n :=
  (DerivedTensor.Right.functor K).map (toNext (fiberModuleCochain F J O) n)

/-- The connecting map `Y_n ⟶ Y_{n+1}[1]` of a stage triangle. -/
def fiberModulePostnikov_connecting (n : ℕ) :
    fiberModulePostnikovY F J O K n ⟶ (fiberModulePostnikovY F J O K (n + 1))⟦(1 : ℤ)⟧ :=
  (DerivedTensor.Right.functor K).map (connecting (fiberModuleCochain F J O) n) ≫
    ((DerivedTensor.Right.functor K).commShiftIso (1 : ℤ)).hom.app
      (y (fiberModuleCochain F J O) (n + 1))

/-- The sequential Postnikov tower of `⋯ → X_2 → X_1 → X_0` in `D(O)` obtained by
tensoring the brutal tower of `fiberModuleCochain` with `K`. -/
def fiberModulePostnikovTower : PostnikovSystem.Tower (fiberTotalDerived F J O) where
  X := fiberModulePostnikovX F J O K
  d := fiberModulePostnikov_d F J O K
  Y := fiberModulePostnikovY F J O K
  toX := fiberModulePostnikov_toX F J O K
  toNext := fiberModulePostnikov_toNext F J O K
  connecting := fiberModulePostnikov_connecting F J O K
  base := sorry
  distinguished := sorry
  comp := sorry

/-- The term object of `fiberModulePostnikovTower K` at `n` is `X_n`. -/
theorem fiberModulePostnikovTower_X (n : ℕ) :
    (fiberModulePostnikovTower F J O K).X n = fiberModulePostnikovX F J O K n :=
  sorry

/-- The auxiliary object of `fiberModulePostnikovTower K` at `n` is `Y_n`. -/
theorem fiberModulePostnikovTower_Y (n : ℕ) :
    (fiberModulePostnikovTower F J O K).Y n = fiberModulePostnikovY F J O K n :=
  sorry

/-- The differential of `fiberModulePostnikovTower K` is `fiberModulePostnikov_d`. -/
theorem fiberModulePostnikovTower_d (n : ℕ) :
    (fiberModulePostnikovTower F J O K).d n = fiberModulePostnikov_d F J O K n :=
  sorry

/-- The comparison `Y_n ⟶ X_n` of `fiberModulePostnikovTower K` is `fiberModulePostnikov_toX`. -/
theorem fiberModulePostnikovTower_toX (n : ℕ) :
    (fiberModulePostnikovTower F J O K).toX n = fiberModulePostnikov_toX F J O K n :=
  sorry

/-- The connecting map of `fiberModulePostnikovTower K` is `fiberModulePostnikov_connecting`. -/
theorem fiberModulePostnikovTower_connecting (n : ℕ) :
    (fiberModulePostnikovTower F J O K).connecting n =
      fiberModulePostnikov_connecting F J O K n :=
  sorry

/-- `X_n` is derived tensor of the degree-zero object `g_{n!} O_n` with `K`. -/
def fiberModulePostnikovXIso (n : ℕ) :
    fiberModulePostnikovX F J O K n ≅
      DerivedTensor.Right.obj
        ((singleFunctor (fiberTotalModules F J O) (0 : ℤ)).obj
          ((fiberModuleComplex F J (fiberTotalRingSheaf F J O)).X n)) K :=
  (DerivedTensor.Right.functor K).mapIso
    ((singleFunctor (fiberTotalModules F J O) (0 : ℤ)).mapIso (fiberModuleCochain_XIso F J O n))

/-- `Y_n` is derived tensor of the shifted brutal stage of `fiberModuleCochain` with `K`. -/
theorem fiberModulePostnikovY_eq (n : ℕ) :
    fiberModulePostnikovY F J O K n =
      (DerivedTensor.Right.functor K).obj (y (fiberModuleCochain F J O) n) :=
  sorry

/-- The successor map `Y_n⟦n⟧ ⟶ Y_{n+1}⟦n+1⟧` of the shifted auxiliary diagram. -/
def fiberModulePostnikovShifted_map (n : ℕ) :
    ((fiberModulePostnikovTower F J O K).Y n)⟦(n : ℤ)⟧ ⟶
      ((fiberModulePostnikovTower F J O K).Y (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧ :=
  ((fiberModulePostnikovTower F J O K).connecting n)⟦(n : ℤ)⟧' ≫
    (shiftFunctorAdd (fiberTotalDerived F J O) (1 : ℤ) n).inv.app
      ((fiberModulePostnikovTower F J O K).Y (n + 1)) ≫
    eqToHom
      (congrArg (fun k : ℤ => ((fiberModulePostnikovTower F J O K).Y (n + 1))⟦k⟧)
        ((add_comm (1 : ℤ) n).trans (Int.natCast_succ n).symm))

/-- The sequential diagram `n ↦ Y_n⟦n⟧` in `D(O)`. -/
def fiberModulePostnikovShifted : ℕ ⥤ fiberTotalDerived F J O :=
  Functor.ofSequence (fiberModulePostnikovShifted_map F J O K)

/-- Evaluating `fiberModulePostnikovShifted K` at `n` recovers `Y_n⟦n⟧`. -/
theorem fiberModulePostnikovShifted_obj (n : ℕ) :
    (fiberModulePostnikovShifted F J O K).obj n =
      ((fiberModulePostnikovTower F J O K).Y n)⟦(n : ℤ)⟧ :=
  sorry

/-- The successor arrow of `fiberModulePostnikovShifted K` is `fiberModulePostnikovShifted_map`. -/
theorem fiberModulePostnikovShifted_map_eq (n : ℕ) :
    (fiberModulePostnikovShifted F J O K).map (homOfLE (Nat.le_add_right n 1)) =
      fiberModulePostnikovShifted_map F J O K n :=
  sorry

end CategoryTheory.Grothendieck
