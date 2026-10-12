/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import stacks_project.Chap69.Lemma_69_12_8_ClosedImmersion
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower

/-!
# Completion of coherent modules on algebraic spaces

The completion of a coherent module along a quasi-coherent ideal sheaf is the
inverse system of coherent ideal-power quotients `F / I ^ n F` on the small
étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The quotient module `F / I ^ n F`, as the cokernel of the inclusion of the
ideal-power product `I ^ n F`. -/
noncomputable def quotientByIdealPower (I : IdealSubobject X) (F : X.Modules)
    (n : ℕ) : X.Modules :=
  cokernel (idealPowerProductSubobject I F n).arrow

/-- The canonical projection `F ⟶ F / I ^ n F`. -/
noncomputable def quotientByIdealPower.π (I : IdealSubobject X) (F : X.Modules)
    (n : ℕ) : F ⟶ quotientByIdealPower I F n :=
  cokernel.π (idealPowerProductSubobject I F n).arrow

/-- The projection `F ⟶ F / I ^ n F` is the cokernel projection of the inclusion
of `I ^ n F`. -/
theorem quotientByIdealPower.π_eq (I : IdealSubobject X) (F : X.Modules)
    (n : ℕ) :
    quotientByIdealPower.π I F n =
      cokernel.π (idealPowerProductSubobject I F n).arrow := sorry

/-- The inclusion of `I ^ (n + 1) F` vanishes after projection to `F / I ^ n F`. -/
theorem quotientByIdealPower.succ_comp_π (I : IdealSubobject X) (F : X.Modules)
    (n : ℕ) :
    (idealPowerProductSubobject I F (n + 1)).arrow ≫
        quotientByIdealPower.π I F n =
      0 := sorry

/-- The transition `F / I ^ (n + 1) F ⟶ F / I ^ n F`. -/
noncomputable def quotientByIdealPower.step (I : IdealSubobject X)
    (F : X.Modules) (n : ℕ) :
    quotientByIdealPower I F (n + 1) ⟶ quotientByIdealPower I F n :=
  cokernel.desc (idealPowerProductSubobject I F (n + 1)).arrow
    (quotientByIdealPower.π I F n) (quotientByIdealPower.succ_comp_π I F n)

/-- A morphism of modules maps `I ^ n F` into `I ^ n G`, hence induces a map of
quotients after composing with the target projection. -/
theorem quotientByIdealPower.map_comp_zero (I : IdealSubobject X)
    {F G : X.Modules} (f : F ⟶ G) (n : ℕ) :
    (idealPowerProductSubobject I F n).arrow ≫
        f ≫ quotientByIdealPower.π I G n =
      0 := sorry

/-- A morphism of modules induces a morphism of ideal-power quotients. -/
noncomputable def quotientByIdealPower.map (I : IdealSubobject X)
    {F G : X.Modules} (f : F ⟶ G) (n : ℕ) :
    quotientByIdealPower I F n ⟶ quotientByIdealPower I G n :=
  cokernel.desc (idealPowerProductSubobject I F n).arrow
    (f ≫ quotientByIdealPower.π I G n)
    (quotientByIdealPower.map_comp_zero I f n)

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

open AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Every ideal-power quotient of a coherent module on a Noetherian algebraic
space is coherent. -/
instance stage_isCoherent [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F : Coh X) (n : ℕ) :
    (quotientByIdealPower I F.obj n).IsCoherent := sorry

/-- Stage `n` of the completion of a coherent module, as a coherent
`𝒪_X`-module. -/
noncomputable def stage [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F : Coh X) (n : ℕ) : Coh X :=
  ⟨quotientByIdealPower I F.obj n, stage_isCoherent I F n⟩

/-- The underlying module of a completion stage is the corresponding
ideal-power quotient. -/
theorem stage_obj [IsNoetherian X] (I : IdealSubobject X) [IsQuasiCoherent I]
    (F : Coh X) (n : ℕ) :
    (stage I F n).obj = quotientByIdealPower I F.obj n := sorry

/-- The transition `F / I ^ (n + 1) F ⟶ F / I ^ n F` in coherent modules. -/
noncomputable def step [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F : Coh X) (n : ℕ) :
    stage I F (n + 1) ⟶ stage I F n :=
  ObjectProperty.homMk (quotientByIdealPower.step I F.obj n)

/-- The explicit inverse system `n ↦ F / I ^ n F` of coherent modules. -/
noncomputable def system [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F : Coh X) :
    SequentialInverseSystem (Coh X) :=
  Functor.ofOpSequence (step I F)

/-- The completion of a coherent module, as an inverse system of coherent
modules. -/
noncomputable abbrev obj [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] (F : Coh X) :
    SequentialInverseSystem (Coh X) :=
  system I F

/-- A morphism of coherent modules induces a morphism on every completion
stage. -/
noncomputable def stageMap [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] {F G : Coh X} (f : F ⟶ G) (n : ℕ) :
    stage I F n ⟶ stage I G n :=
  ObjectProperty.homMk (quotientByIdealPower.map I f.hom n)

/-- Stage maps commute with the successor transitions of coherent completion. -/
theorem stageMap_naturality [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] {F G : Coh X} (f : F ⟶ G) (n : ℕ) :
    step I F n ≫ stageMap I f n = stageMap I f (n + 1) ≫ step I G n := sorry

/-- Stage maps satisfy the successor equation used by `NatTrans.ofOpSequence`. -/
theorem systemMap_naturality [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] {F G : Coh X} (f : F ⟶ G) (n : ℕ) :
    (system I F).map (homOfLE (Nat.le_add_right n 1)).op ≫ stageMap I f n =
      stageMap I f (n + 1) ≫
        (system I G).map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The morphism of completion inverse systems induced by a morphism of
coherent modules. -/
noncomputable def systemMap [IsNoetherian X] (I : IdealSubobject X)
    [IsQuasiCoherent I] {F G : Coh X} (f : F ⟶ G) :
    system I F ⟶ system I G :=
  NatTrans.ofOpSequence (stageMap I f) (systemMap_naturality I f)

end AlgebraicGeometry.AlgebraicSpace.CoherentCompletion
