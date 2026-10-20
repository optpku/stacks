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
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberResolution

/-!
# Module Postnikov towers on fiberwise simplicial sites

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

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [UnivLE.{max u v, w}]
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

/-- The cochain complex obtained by embedding
`… → g_{2!} O_2 → g_{1!} O_1 → g_{0!} O_0` along `n ↦ -n`. -/
def fiberModuleCochain : CochainComplex (ringedSiteModuleCategory.{_, _, w, w} (topology F J) O) ℤ :=
  (fiberModuleComplex F J (Sheaf.ringSheafOfComm O)).extend embeddingDownNat

/-- The embedded resolution is concentrated in cohomological degrees `≤ 0`. -/
instance fiberModuleCochain_isStrictlyLE : (fiberModuleCochain F J O).IsStrictlyLE 0 := by
  unfold fiberModuleCochain
  infer_instance

/-- Degree `-n` of `fiberModuleCochain` is the sheaf of modules `g_{n!} O_n`. -/
def fiberModuleCochain_XIso (n : ℕ) :
    (fiberModuleCochain F J O).X (CochainComplex.Brutal.Tower.index n) ≅
      (fiberModuleComplex F J (Sheaf.ringSheafOfComm O)).X n :=
  (fiberModuleComplex F J (Sheaf.ringSheafOfComm O)).extendXIso embeddingDownNat rfl

/-- Canonical derived-category structure on modules over the commutative ring sheaf `O`. -/
noncomputable instance fiberTotalModules_hasDerivedCategory :
    HasDerivedCategory (ringedSiteModuleCategory.{_, _, w, w} (topology F J) O) :=
  moduleCategoryHasDerivedCategory (𝒪 := O)

variable (K : RingedSiteDerived (topology F J) O)

/-- The term `X_n = (g_{n!} O_n) ⊗^L_O K` in `D(O)`. -/
def fiberModulePostnikovX (n : ℕ) : RingedSiteDerived (topology F J) O :=
  (DerivedTensor.Right.functor K).obj (x (fiberModuleCochain F J O) n)

/-- The auxiliary object
`Y_n = (g_{n!} O_n → ⋯ → g_{0!} O_0)[-n] ⊗^L_O K` in `D(O)`. -/
def fiberModulePostnikovY (n : ℕ) : RingedSiteDerived (topology F J) O :=
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

/-- The degree-zero comparison of the tensored resolution is invertible. -/
instance fiberModulePostnikov_base : IsIso (fiberModulePostnikov_toX F J O K 0) :=
  sorry

/-- The canonical maps of the tensored brutal resolution form distinguished triangles. -/
theorem fiberModulePostnikov_distinguished (n : ℕ) :
    Triangle.mk (fiberModulePostnikov_toX F J O K (n + 1))
      (fiberModulePostnikov_toNext F J O K n) (fiberModulePostnikov_connecting F J O K n) ∈
        distTriang (RingedSiteDerived (topology F J) O) :=
  sorry

/-- The two comparison maps recover the alternating-face differential after tensoring. -/
theorem fiberModulePostnikov_comp (n : ℕ) :
    fiberModulePostnikov_toNext F J O K n ≫ fiberModulePostnikov_toX F J O K n =
      fiberModulePostnikov_d F J O K n :=
  sorry

/-- The sequential Postnikov tower of `⋯ → X_2 → X_1 → X_0` in `D(O)` obtained by
tensoring the brutal tower of `fiberModuleCochain` with `K`. -/
def fiberModulePostnikovTower : PostnikovSystem.Tower (RingedSiteDerived (topology F J) O) where
  X := fiberModulePostnikovX F J O K
  d := fiberModulePostnikov_d F J O K
  Y := fiberModulePostnikovY F J O K
  toX := fiberModulePostnikov_toX F J O K
  toNext := fiberModulePostnikov_toNext F J O K
  connecting := fiberModulePostnikov_connecting F J O K
  base := fiberModulePostnikov_base F J O K
  distinguished := fiberModulePostnikov_distinguished F J O K
  comp := fiberModulePostnikov_comp F J O K

/-- The term object of `fiberModulePostnikovTower K` at `n` is `X_n`. -/
theorem fiberModulePostnikovTower_X (n : ℕ) :
    (fiberModulePostnikovTower F J O K).X n = fiberModulePostnikovX F J O K n :=
  rfl

/-- The auxiliary object of `fiberModulePostnikovTower K` at `n` is `Y_n`. -/
theorem fiberModulePostnikovTower_Y (n : ℕ) :
    (fiberModulePostnikovTower F J O K).Y n = fiberModulePostnikovY F J O K n :=
  rfl

/-- The differential of `fiberModulePostnikovTower K` is `fiberModulePostnikov_d`. -/
theorem fiberModulePostnikovTower_d (n : ℕ) :
    (fiberModulePostnikovTower F J O K).d n = fiberModulePostnikov_d F J O K n :=
  rfl

/-- The comparison `Y_n ⟶ X_n` of `fiberModulePostnikovTower K` is `fiberModulePostnikov_toX`. -/
theorem fiberModulePostnikovTower_toX (n : ℕ) :
    (fiberModulePostnikovTower F J O K).toX n = fiberModulePostnikov_toX F J O K n :=
  rfl

/-- The connecting map of `fiberModulePostnikovTower K` is `fiberModulePostnikov_connecting`. -/
theorem fiberModulePostnikovTower_connecting (n : ℕ) :
    (fiberModulePostnikovTower F J O K).connecting n =
      fiberModulePostnikov_connecting F J O K n :=
  rfl

/-- `X_n` is derived tensor of the degree-zero object `g_{n!} O_n` with `K`. -/
def fiberModulePostnikovXIso (n : ℕ) :
    fiberModulePostnikovX F J O K n ≅
      DerivedTensor.Right.obj
        ((singleFunctor (ringedSiteModuleCategory.{_, _, w, w} (topology F J) O) (0 : ℤ)).obj
          ((fiberModuleComplex F J (Sheaf.ringSheafOfComm O)).X n)) K :=
  (DerivedTensor.Right.functor K).mapIso
    ((singleFunctor (ringedSiteModuleCategory.{_, _, w, w} (topology F J) O) (0 : ℤ)).mapIso (fiberModuleCochain_XIso F J O n))

/-- The successor map `Y_n⟦n⟧ ⟶ Y_{n+1}⟦n+1⟧` of the shifted auxiliary diagram. -/
def fiberModulePostnikovShifted_map (n : ℕ) :
    ((fiberModulePostnikovTower F J O K).Y n)⟦(n : ℤ)⟧ ⟶
      ((fiberModulePostnikovTower F J O K).Y (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧ :=
  ((fiberModulePostnikovTower F J O K).connecting n)⟦(n : ℤ)⟧' ≫
    (shiftFunctorAdd (RingedSiteDerived (topology F J) O) (1 : ℤ) n).inv.app
      ((fiberModulePostnikovTower F J O K).Y (n + 1)) ≫
    eqToHom
      (congrArg (fun k : ℤ => ((fiberModulePostnikovTower F J O K).Y (n + 1))⟦k⟧)
        ((add_comm (1 : ℤ) n).trans (Int.natCast_succ n).symm))

/-- The sequential diagram `n ↦ Y_n⟦n⟧` in `D(O)`. -/
def fiberModulePostnikovShifted : ℕ ⥤ RingedSiteDerived (topology F J) O :=
  Functor.ofSequence (fiberModulePostnikovShifted_map F J O K)

/-- Evaluating `fiberModulePostnikovShifted K` at `n` recovers `Y_n⟦n⟧`. -/
theorem fiberModulePostnikovShifted_obj (n : ℕ) :
    (fiberModulePostnikovShifted F J O K).obj n =
      ((fiberModulePostnikovTower F J O K).Y n)⟦(n : ℤ)⟧ :=
  rfl

/-- The successor arrow of `fiberModulePostnikovShifted K` is `fiberModulePostnikovShifted_map`. -/
theorem fiberModulePostnikovShifted_map_eq (n : ℕ) :
    (fiberModulePostnikovShifted F J O K).map (homOfLE (Nat.le_add_right n 1)) =
      fiberModulePostnikovShifted_map F J O K n := by
  exact Functor.ofSequence_map_homOfLE_succ (fiberModulePostnikovShifted_map F J O K) n

/-- An arbitrary derived module object is a homotopy colimit of the shifted
stages of its canonical tensored resolution. -/
theorem fiberModulePostnikov_isHomotopyColimit :
    HomotopyColimit.IsOf (fiberModulePostnikovShifted F J O K) K :=
  sorry

end CategoryTheory.Grothendieck
