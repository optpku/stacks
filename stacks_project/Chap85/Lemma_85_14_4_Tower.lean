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
public import stacks_project.Chap85.Lemma_85_10_1_Complex

/-!
# Sequential Postnikov tower of `g_{n!} O_n` tensored with an object of `D(O)`

In Situation 85.3.3 case A, embed the alternating-face resolution
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

namespace CategoryTheory.SimplicialSites

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

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
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

/-- The underlying ring sheaf of a commutative ring sheaf on `C_total`. -/
abbrev totalRingSheaf : Sheaf (topology C J) RingCat.{w} :=
  Sheaf.ringSheafOfComm O

/-- Unfolding `totalRingSheaf` recovers `Sheaf.ringSheafOfComm`. -/
theorem totalRingSheaf_eq : totalRingSheaf C J O = Sheaf.ringSheafOfComm O :=
  sorry

/-- Sheaves of modules over the underlying ring sheaf of `O` on `C_total`. -/
abbrev totalModules :=
  SheafOfModules.{w} (totalRingSheaf C J O)

/-- Unfolding `totalModules` recovers sheaves of modules over `Sheaf.ringSheafOfComm O`. -/
theorem totalModules_eq :
    totalModules C J O = SheafOfModules.{w} (Sheaf.ringSheafOfComm O) :=
  sorry

/-- The cochain complex obtained by embedding
`… → g_{2!} O_2 → g_{1!} O_1 → g_{0!} O_0` along `n ↦ -n`. -/
def moduleCochain : CochainComplex (totalModules C J O) ℤ :=
  (moduleComplex C J (totalRingSheaf C J O)).extend embeddingDownNat

/-- The embedded resolution is concentrated in cohomological degrees `≤ 0`. -/
instance moduleCochain_isStrictlyLE : (moduleCochain C J O).IsStrictlyLE 0 :=
  sorry

/-- Degree `-n` of `moduleCochain` is the sheaf of modules `g_{n!} O_n`. -/
def moduleCochain_XIso (n : ℕ) :
    (moduleCochain C J O).X (CochainComplex.Brutal.Tower.index n) ≅
      (moduleComplex C J (totalRingSheaf C J O)).X n :=
  (moduleComplex C J (totalRingSheaf C J O)).extendXIso embeddingDownNat rfl

variable [UnivLE.{max u v, w}]

/-- Canonical derived-category structure on modules over the commutative ring sheaf `O`. -/
noncomputable instance totalModules_hasDerivedCategory :
    HasDerivedCategory (totalModules C J O) :=
  RingedSite.Hom.moduleCat_hasDerivedCategory.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} (topology C J) O)

/-- The derived category `D(O)` of modules on `C_total`. -/
abbrev totalDerived :=
  RingedSite.Hom.ModuleDerived.{w}
    (RingedSite.ofCommRingSheaf.{u, v, w} (topology C J) O)

/-- Unfolding `totalDerived` recovers `DerivedCategory` of `totalModules`. -/
theorem totalDerived_eq : totalDerived C J O = DerivedCategory (totalModules C J O) :=
  sorry

/-- Canonical tensor product on modules over the commutative ring sheaf `O`. -/
noncomputable instance totalModules_monoidalCategory :
    MonoidalCategory (totalModules C J O) :=
  SheafOfModules.RingedSite.moduleMonoidalCategory O

/-- The tensor product of `O`-modules is additive in both variables. -/
instance totalModules_monoidalPreadditive :
    MonoidalPreadditive (totalModules C J O) :=
  SheafOfModules.RingedSite.monoidalPreadditive

/-- Unbounded cochain tensor totalization exists for modules over `O`. -/
instance totalModules_hasMapBifunctor
    (X Y : CochainComplex (totalModules C J O) ℤ) :
    HomologicalComplex.HasMapBifunctor X Y
      (curriedTensor (totalModules C J O)) (up ℤ) :=
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor O X Y

variable [HasRightDerivedTensor (totalModules C J O)]

/-- The canonical sequential Postnikov tower of the embedded resolution, before
tensoring with an object of `D(O)`. -/
def moduleUnitPostnikovTower : PostnikovSystem.Tower (totalDerived C J O) :=
  tower (moduleCochain C J O)

/-- The unit tower is the brutal derived Postnikov tower of `moduleCochain`. -/
theorem moduleUnitPostnikovTower_eq :
    moduleUnitPostnikovTower C J O = tower (moduleCochain C J O) :=
  sorry

variable (K : totalDerived C J O)

/-- The term `X_n = (g_{n!} O_n) ⊗^L_O K` in `D(O)`. -/
def modulePostnikovX (n : ℕ) : totalDerived C J O :=
  (DerivedTensor.Right.functor K).obj (x (moduleCochain C J O) n)

/-- The auxiliary object
`Y_n = (g_{n!} O_n → ⋯ → g_{0!} O_0)[-n] ⊗^L_O K` in `D(O)`. -/
def modulePostnikovY (n : ℕ) : totalDerived C J O :=
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

/-- The sequential Postnikov tower of `⋯ → X_2 → X_1 → X_0` in `D(O)` obtained by
tensoring the brutal tower of `moduleCochain` with `K`. -/
def modulePostnikovTower : PostnikovSystem.Tower (totalDerived C J O) where
  X := modulePostnikovX C J O K
  d := modulePostnikov_d C J O K
  Y := modulePostnikovY C J O K
  toX := modulePostnikov_toX C J O K
  toNext := modulePostnikov_toNext C J O K
  connecting := modulePostnikov_connecting C J O K
  base := sorry
  distinguished := sorry
  comp := sorry

/-- The term object of `modulePostnikovTower K` at `n` is `X_n`. -/
theorem modulePostnikovTower_X (n : ℕ) :
    (modulePostnikovTower C J O K).X n = modulePostnikovX C J O K n :=
  sorry

/-- The auxiliary object of `modulePostnikovTower K` at `n` is `Y_n`. -/
theorem modulePostnikovTower_Y (n : ℕ) :
    (modulePostnikovTower C J O K).Y n = modulePostnikovY C J O K n :=
  sorry

/-- The differential of `modulePostnikovTower K` is `modulePostnikov_d`. -/
theorem modulePostnikovTower_d (n : ℕ) :
    (modulePostnikovTower C J O K).d n = modulePostnikov_d C J O K n :=
  sorry

/-- The comparison `Y_n ⟶ X_n` of `modulePostnikovTower K` is `modulePostnikov_toX`. -/
theorem modulePostnikovTower_toX (n : ℕ) :
    (modulePostnikovTower C J O K).toX n = modulePostnikov_toX C J O K n :=
  sorry

/-- The connecting map of `modulePostnikovTower K` is `modulePostnikov_connecting`. -/
theorem modulePostnikovTower_connecting (n : ℕ) :
    (modulePostnikovTower C J O K).connecting n =
      modulePostnikov_connecting C J O K n :=
  sorry

/-- `X_n` is derived tensor of the degree-zero object `g_{n!} O_n` with `K`. -/
def modulePostnikovXIso (n : ℕ) :
    modulePostnikovX C J O K n ≅
      DerivedTensor.Right.obj
        ((singleFunctor (totalModules C J O) (0 : ℤ)).obj
          ((moduleComplex C J (totalRingSheaf C J O)).X n)) K :=
  (DerivedTensor.Right.functor K).mapIso
    ((singleFunctor (totalModules C J O) (0 : ℤ)).mapIso (moduleCochain_XIso C J O n))

/-- `Y_n` is derived tensor of the shifted brutal stage of `moduleCochain` with `K`. -/
theorem modulePostnikovY_eq (n : ℕ) :
    modulePostnikovY C J O K n =
      (DerivedTensor.Right.functor K).obj (y (moduleCochain C J O) n) :=
  sorry

/-- The successor map `Y_n⟦n⟧ ⟶ Y_{n+1}⟦n+1⟧` of the shifted auxiliary diagram. -/
def modulePostnikovShifted_map (n : ℕ) :
    ((modulePostnikovTower C J O K).Y n)⟦(n : ℤ)⟧ ⟶
      ((modulePostnikovTower C J O K).Y (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧ :=
  ((modulePostnikovTower C J O K).connecting n)⟦(n : ℤ)⟧' ≫
    (shiftFunctorAdd (totalDerived C J O) (1 : ℤ) n).inv.app
      ((modulePostnikovTower C J O K).Y (n + 1)) ≫
    eqToHom
      (congrArg (fun k : ℤ => ((modulePostnikovTower C J O K).Y (n + 1))⟦k⟧)
        ((add_comm (1 : ℤ) n).trans (Int.natCast_succ n).symm))

/-- The sequential diagram `n ↦ Y_n⟦n⟧` in `D(O)`. -/
def modulePostnikovShifted : ℕ ⥤ totalDerived C J O :=
  Functor.ofSequence (modulePostnikovShifted_map C J O K)

/-- Evaluating `modulePostnikovShifted K` at `n` recovers `Y_n⟦n⟧`. -/
theorem modulePostnikovShifted_obj (n : ℕ) :
    (modulePostnikovShifted C J O K).obj n =
      ((modulePostnikovTower C J O K).Y n)⟦(n : ℤ)⟧ :=
  sorry

/-- The successor arrow of `modulePostnikovShifted K` is `modulePostnikovShifted_map`. -/
theorem modulePostnikovShifted_map_eq (n : ℕ) :
    (modulePostnikovShifted C J O K).map (homOfLE (Nat.le_add_right n 1)) =
      modulePostnikovShifted_map C J O K n :=
  sorry

end CategoryTheory.SimplicialSites
