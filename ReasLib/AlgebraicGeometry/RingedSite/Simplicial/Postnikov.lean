/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Derived.Postnikov
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Definition
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Resolution

/-!
# Module Postnikov towers on simplicial sites

The alternating-face lower-shriek unit resolution, embedded in nonpositive
cohomological degrees, gives canonical Postnikov towers after derived tensoring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory
open ComplexShape DerivedCategory HomologicalComplex
open CochainComplex.Brutal.Derived.Postnikov
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [UnivLE.{max u v, w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) CommRingCat.{w})
variable [(topology C J).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J (Sheaf.ringSheafOfComm O) n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J (Sheaf.ringSheafOfComm O) φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The cochain complex obtained by embedding
`… → g_{2!} O_2 → g_{1!} O_1 → g_{0!} O_0` along `n ↦ -n`. -/
def moduleCochain : CochainComplex (ringedSiteModuleCategory.{_, _, w, w} (topology C J) O) ℤ :=
  (moduleComplex C J (Sheaf.ringSheafOfComm O)).extend embeddingDownNat

/-- The embedded resolution is concentrated in cohomological degrees `≤ 0`. -/
instance moduleCochain_isStrictlyLE : (moduleCochain C J O).IsStrictlyLE 0 := by
  unfold moduleCochain
  infer_instance

/-- Degree `-n` of `moduleCochain` is the sheaf of modules `g_{n!} O_n`. -/
def moduleCochain_XIso (n : ℕ) :
    (moduleCochain C J O).X (CochainComplex.Brutal.Tower.index n) ≅
      (moduleComplex C J (Sheaf.ringSheafOfComm O)).X n :=
  (moduleComplex C J (Sheaf.ringSheafOfComm O)).extendXIso embeddingDownNat rfl

/-- Canonical derived-category structure on modules over the commutative ring sheaf `O`. -/
noncomputable instance totalModules_hasDerivedCategory :
    HasDerivedCategory (ringedSiteModuleCategory.{_, _, w, w} (topology C J) O) :=
  moduleCategoryHasDerivedCategory (𝒪 := O)

variable (K : RingedSiteDerived (topology C J) O)

/-- The term `X_n = (g_{n!} O_n) ⊗^L_O K` in `D(O)`. -/
def modulePostnikovX (n : ℕ) : RingedSiteDerived (topology C J) O :=
  (DerivedTensor.Right.functor K).obj (x (moduleCochain C J O) n)

/-- The auxiliary object
`Y_n = (g_{n!} O_n → ⋯ → g_{0!} O_0)[-n] ⊗^L_O K` in `D(O)`. -/
def modulePostnikovY (n : ℕ) : RingedSiteDerived (topology C J) O :=
  (DerivedTensor.Right.functor K).obj (y (moduleCochain C J O) n)

/-- The differential `X_{n+1} ⟶ X_n` induced by the alternating-face maps. -/
def modulePostnikov_d (n : ℕ) :
    modulePostnikovX C J O K (n + 1) ⟶ modulePostnikovX C J O K n :=
  (DerivedTensor.Right.functor K).map (d (moduleCochain C J O) n)

/-- The canonical comparison `Y_n ⟶ X_n`. -/
def modulePostnikov_toX (n : ℕ) :
    modulePostnikovY C J O K n ⟶ modulePostnikovX C J O K n :=
  (DerivedTensor.Right.functor K).map (toX (moduleCochain C J O) n)

/-- The second map `X_{n+1} ⟶ Y_n` of a stage triangle. -/
def modulePostnikov_toNext (n : ℕ) :
    modulePostnikovX C J O K (n + 1) ⟶ modulePostnikovY C J O K n :=
  (DerivedTensor.Right.functor K).map (toNext (moduleCochain C J O) n)

/-- The connecting map `Y_n ⟶ Y_{n+1}[1]` of a stage triangle. -/
def modulePostnikov_connecting (n : ℕ) :
    modulePostnikovY C J O K n ⟶ (modulePostnikovY C J O K (n + 1))⟦(1 : ℤ)⟧ :=
  (DerivedTensor.Right.functor K).map (connecting (moduleCochain C J O) n) ≫
    ((DerivedTensor.Right.functor K).commShiftIso (1 : ℤ)).hom.app
      (y (moduleCochain C J O) (n + 1))

/-- The degree-zero comparison of the tensored resolution is invertible. -/
instance modulePostnikov_base : IsIso (modulePostnikov_toX C J O K 0) :=
  sorry

/-- The canonical maps of the tensored brutal resolution form distinguished triangles. -/
theorem modulePostnikov_distinguished (n : ℕ) :
    Triangle.mk (modulePostnikov_toX C J O K (n + 1))
      (modulePostnikov_toNext C J O K n) (modulePostnikov_connecting C J O K n) ∈
        distTriang (RingedSiteDerived (topology C J) O) :=
  sorry

/-- The two comparison maps recover the alternating-face differential after tensoring. -/
theorem modulePostnikov_comp (n : ℕ) :
    modulePostnikov_toNext C J O K n ≫ modulePostnikov_toX C J O K n =
      modulePostnikov_d C J O K n :=
  sorry

/-- The sequential Postnikov tower of `⋯ → X_2 → X_1 → X_0` in `D(O)` obtained by
tensoring the brutal tower of `moduleCochain` with `K`. -/
def modulePostnikovTower : PostnikovSystem.Tower (RingedSiteDerived (topology C J) O) where
  X := modulePostnikovX C J O K
  d := modulePostnikov_d C J O K
  Y := modulePostnikovY C J O K
  toX := modulePostnikov_toX C J O K
  toNext := modulePostnikov_toNext C J O K
  connecting := modulePostnikov_connecting C J O K
  base := modulePostnikov_base C J O K
  distinguished := modulePostnikov_distinguished C J O K
  comp := modulePostnikov_comp C J O K

/-- The term object of `modulePostnikovTower K` at `n` is `X_n`. -/
theorem modulePostnikovTower_X (n : ℕ) :
    (modulePostnikovTower C J O K).X n = modulePostnikovX C J O K n :=
  rfl

/-- The auxiliary object of `modulePostnikovTower K` at `n` is `Y_n`. -/
theorem modulePostnikovTower_Y (n : ℕ) :
    (modulePostnikovTower C J O K).Y n = modulePostnikovY C J O K n :=
  rfl

/-- The differential of `modulePostnikovTower K` is `modulePostnikov_d`. -/
theorem modulePostnikovTower_d (n : ℕ) :
    (modulePostnikovTower C J O K).d n = modulePostnikov_d C J O K n :=
  rfl

/-- The comparison `Y_n ⟶ X_n` of `modulePostnikovTower K` is `modulePostnikov_toX`. -/
theorem modulePostnikovTower_toX (n : ℕ) :
    (modulePostnikovTower C J O K).toX n = modulePostnikov_toX C J O K n :=
  rfl

/-- The connecting map of `modulePostnikovTower K` is `modulePostnikov_connecting`. -/
theorem modulePostnikovTower_connecting (n : ℕ) :
    (modulePostnikovTower C J O K).connecting n =
      modulePostnikov_connecting C J O K n :=
  rfl

/-- `X_n` is derived tensor of the degree-zero object `g_{n!} O_n` with `K`. -/
def modulePostnikovXIso (n : ℕ) :
    modulePostnikovX C J O K n ≅
      DerivedTensor.Right.obj
        ((singleFunctor (ringedSiteModuleCategory.{_, _, w, w} (topology C J) O) (0 : ℤ)).obj
          ((moduleComplex C J (Sheaf.ringSheafOfComm O)).X n)) K :=
  (DerivedTensor.Right.functor K).mapIso
    ((singleFunctor (ringedSiteModuleCategory.{_, _, w, w} (topology C J) O) (0 : ℤ)).mapIso (moduleCochain_XIso C J O n))

/-- The successor map `Y_n⟦n⟧ ⟶ Y_{n+1}⟦n+1⟧` of the shifted auxiliary diagram. -/
def modulePostnikovShifted_map (n : ℕ) :
    ((modulePostnikovTower C J O K).Y n)⟦(n : ℤ)⟧ ⟶
      ((modulePostnikovTower C J O K).Y (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧ :=
  ((modulePostnikovTower C J O K).connecting n)⟦(n : ℤ)⟧' ≫
    (shiftFunctorAdd (RingedSiteDerived (topology C J) O) (1 : ℤ) n).inv.app
      ((modulePostnikovTower C J O K).Y (n + 1)) ≫
    eqToHom
      (congrArg (fun k : ℤ => ((modulePostnikovTower C J O K).Y (n + 1))⟦k⟧)
        ((add_comm (1 : ℤ) n).trans (Int.natCast_succ n).symm))

/-- The sequential diagram `n ↦ Y_n⟦n⟧` in `D(O)`. -/
def modulePostnikovShifted : ℕ ⥤ RingedSiteDerived (topology C J) O :=
  Functor.ofSequence (modulePostnikovShifted_map C J O K)

/-- Evaluating `modulePostnikovShifted K` at `n` recovers `Y_n⟦n⟧`. -/
theorem modulePostnikovShifted_obj (n : ℕ) :
    (modulePostnikovShifted C J O K).obj n =
      ((modulePostnikovTower C J O K).Y n)⟦(n : ℤ)⟧ :=
  rfl

/-- The successor arrow of `modulePostnikovShifted K` is `modulePostnikovShifted_map`. -/
theorem modulePostnikovShifted_map_eq (n : ℕ) :
    (modulePostnikovShifted C J O K).map (homOfLE (Nat.le_add_right n 1)) =
      modulePostnikovShifted_map C J O K n := by
  exact Functor.ofSequence_map_homOfLE_succ (modulePostnikovShifted_map C J O K) n

/-- An arbitrary derived module object is a homotopy colimit of the shifted
stages of its canonical tensored resolution. -/
theorem modulePostnikov_isHomotopyColimit :
    HomotopyColimit.IsOf (modulePostnikovShifted C J O K) K :=
  sorry

end CategoryTheory.SimplicialSites
