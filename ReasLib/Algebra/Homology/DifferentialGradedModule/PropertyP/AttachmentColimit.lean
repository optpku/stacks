/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.AttachmentTower

/-!
# Private proposal: the quotient colimit of the actual attachment tower

The carrier is the direct sum of stage carriers modulo the image of `id - shift`.
All descents specify their functions before the well-definedness laws.
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace DifferentialGradedModule.PropertyP.PrivateConstruction

variable {R : Type u} [CommRing R] {A : CochainDGAlgebra.{u, v} R}

/-- The actual direct sum of the actual stages. -/
abbrev towerSum (M : DifferentialGradedModule.{u, v} A) :
    DifferentialGradedModule.{u, v} A :=
  Coproduct.obj (fun k : ℕ ↦ (stage M k).obj)

/-- Include one stage into the actual direct sum. -/
def sumInclusion (M : DifferentialGradedModule.{u, v} A) (k : ℕ) :
    (stage M k).obj ⟶ towerSum M :=
  Coproduct.ι (fun k : ℕ ↦ (stage M k).obj) k

/-- The shift on the direct sum is induced by the tower's actual transition maps. -/
def sumShift (M : DifferentialGradedModule.{u, v} A) : towerSum M ⟶ towerSum M :=
  Coproduct.desc (fun k : ℕ ↦ (stage M k).obj)
    (fun k ↦ step M k ≫ sumInclusion M (k + 1))

/-- Relations identifying a stage element with its image in the next stage. -/
def transitionRelations (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    Submodule R ((towerSum M).X n) :=
  LinearMap.range (LinearMap.id - (sumShift M).hom n)

/-- The degreewise quotient carrier of the sequential colimit. -/
abbrev colimitDegree (M : DifferentialGradedModule.{u, v} A) (n : ℤ) : ModuleCat.{v} R :=
  ModuleCat.of R ((towerSum M).X n ⧸ transitionRelations M n)

/-- The actual projection from the direct sum to the quotient. -/
def quotientLinear (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (towerSum M).X n →ₗ[R] colimitDegree M n :=
  (transitionRelations M n).mkQ

/-- The quotient differential descends the coordinatewise stage differential. -/
def colimitDifferential (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    colimitDegree M n →ₗ[R] colimitDegree M (n + 1) :=
  (transitionRelations M n).liftQ
    ((quotientLinear M (n + 1)).comp ((towerSum M).d n)) (by sorry)

/-- The actual balanced action on a raw direct-sum element, followed by quotient projection. -/
def rawQuotientAction (M : DifferentialGradedModule.{u, v} A) (p i : ℤ) :
    (towerSum M).X p →ₗ[R] A.X i →ₗ[R] colimitDegree M (p + i) where
  toFun x := (quotientLinear M (p + i)).comp ((towerSum M).smul p i x)
  map_add' := by sorry
  map_smul' := by sorry

/-- The quotient right action descends the coordinatewise right action of the stages. -/
def colimitAction (M : DifferentialGradedModule.{u, v} A) (p i : ℤ) :
    colimitDegree M p →ₗ[R] A.X i →ₗ[R] colimitDegree M (p + i) :=
  (transitionRelations M p).liftQ (rawQuotientAction M p i) (by sorry)

/-- The actual omega-stage DG module, with quotient differential and right `A`-action. -/
def omegaObj (M : DifferentialGradedModule.{u, v} A) :
    DifferentialGradedModule.{u, v} A where
  X := colimitDegree M
  d := colimitDifferential M
  smul := colimitAction M
  d_sq := by sorry
  smul_one := by sorry
  smul_mul := by sorry
  comm_d := by sorry

/-- The actual quotient map as a DG morphism. -/
def sumToOmega (M : DifferentialGradedModule.{u, v} A) : towerSum M ⟶ omegaObj M where
  hom := quotientLinear M
  comm_d := by sorry
  comm_smul := by sorry

/-- The cocone injection is stage inclusion followed by the actual quotient map. -/
def omegaι (M : DifferentialGradedModule.{u, v} A) (k : ℕ) :
    (stage M k).obj ⟶ omegaObj M :=
  sumInclusion M k ≫ sumToOmega M

/-- Extend the compatible stage augmentations over the direct sum. -/
def sumπ (M : DifferentialGradedModule.{u, v} A) : towerSum M ⟶ M :=
  Coproduct.desc (fun k : ℕ ↦ (stage M k).obj) (fun k ↦ (stage M k).π)

/-- The actual augmentation `P(M) → M` is the quotient descent of the stage augmentations. -/
def omegaπ (M : DifferentialGradedModule.{u, v} A) : omegaObj M ⟶ M where
  hom n := (transitionRelations M n).liftQ ((sumπ M).hom n) (by sorry)
  comm_d := by sorry
  comm_smul := by sorry

/-- The direct-sum map induced by all finite-stage comparisons. -/
def sumMap {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    towerSum M ⟶ towerSum N :=
  Coproduct.desc (fun k : ℕ ↦ (stage M k).obj)
    (fun k ↦ (stageMap f k).hom ≫ sumInclusion N k)

/-- The actual functorial map on the omega-stage quotients. -/
def omegaMap {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    omegaObj M ⟶ omegaObj N where
  hom n := (transitionRelations M n).liftQ
    ((quotientLinear N n).comp ((sumMap f).hom n)) (by sorry)
  comm_d := by sorry
  comm_smul := by sorry

/-- Explicit quotient descent of any compatible family of DG maps out of the stages. -/
def omegaDesc (M N : DifferentialGradedModule.{u, v} A)
    (f : ∀ k, (stage M k).obj ⟶ N)
    (hf : ∀ k, step M k ≫ f (k + 1) = f k) : omegaObj M ⟶ N where
  hom n := (transitionRelations M n).liftQ
    ((Coproduct.desc (fun k : ℕ ↦ (stage M k).obj) f).hom n) (by sorry)
  comm_d := by sorry
  comm_smul := by sorry

/-- The actual replacement functor; its map is the quotient of the recursively specified maps. -/
def omegaFunctor (A : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedModule.{u, v} A ⥤ DifferentialGradedModule.{u, v} A where
  obj := omegaObj
  map := omegaMap
  map_id := by sorry
  map_comp := by sorry

/-- The actual augmentation transformation has the already specified degreewise quotient descents. -/
def omegaAugmentation (A : CochainDGAlgebra.{u, v} R) :
    omegaFunctor A ⟶ 𝟭 (DifferentialGradedModule.{u, v} A) where
  app := omegaπ
  naturality := by sorry

/-- The specified omega cocone commutes with the actual transition maps. -/
theorem step_omegaι (M : DifferentialGradedModule.{u, v} A) (k : ℕ) :
    step M k ≫ omegaι M (k + 1) = omegaι M k := by sorry

/-- Stage augmentation is exactly the restriction of the omega augmentation. -/
theorem omegaι_π (M : DifferentialGradedModule.{u, v} A) (k : ℕ) :
    omegaι M k ≫ omegaπ M = (stage M k).π := by sorry

/-- A finite upper bound for all stage indices occurring in a raw direct-sum element. -/
def representativeBound (M : DifferentialGradedModule.{u, v} A) (n : ℤ)
    (x : (towerSum M).X n) : ℕ := by
  classical
  exact x.support.sup id

/-- Move the finitely many raw coordinates to one common stage using actual transition maps. -/
def rawRepresentative (M : DifferentialGradedModule.{u, v} A) (n : ℤ)
    (x : (towerSum M).X n) : (stage M (representativeBound M n x)).obj.X n := by
  classical
  let raw : DirectSum ℕ (fun k ↦ (stage M k).obj.X n) := x
  exact raw.support.sum (fun k ↦
    if h : k ≤ representativeBound M n x then
      ((Functor.ofSequence (step M)).map (homOfLE h)).hom n (raw k)
    else 0)

/-- A specified stage representative, using only the native representative of a genuine quotient
and the finite support bound. No representative is selected from an admitted existence theorem. -/
def omegaRepresentative (M : DifferentialGradedModule.{u, v} A) (n : ℤ)
    (x : (omegaObj M).X n) : Σ k : ℕ, (stage M k).obj.X n :=
  let raw : (towerSum M).X n := Quotient.out x
  ⟨representativeBound M n raw, rawRepresentative M n raw⟩

/-- The explicit stage representative projects to the original quotient element. -/
theorem omegaRepresentative_spec (M : DifferentialGradedModule.{u, v} A) (n : ℤ)
    (x : (omegaObj M).X n) :
    (omegaι M (omegaRepresentative M n x).1).hom n (omegaRepresentative M n x).2 = x := by
  sorry

/-- A stage representative of a closed quotient element is closed: all transition maps are the
specified split injections, so no differential can vanish only at the limit. -/
theorem omegaRepresentative_closed (M : DifferentialGradedModule.{u, v} A) (n : ℤ)
    (x : (omegaObj M).X n) (hx : (omegaObj M).d n x = 0) :
    (stage M (omegaRepresentative M n x).1).obj.d n (omegaRepresentative M n x).2 = 0 := by
  sorry

end DifferentialGradedModule.PropertyP.PrivateConstruction
