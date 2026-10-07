module

public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import stacks_project.Chap62.Lemma_62_4_1_Specialization

/-!
# Families of cycles on fibres

This file names the additive group of families of `r`-cycles on scheme-theoretic
fibres of a morphism, and the fibrewise base-change homomorphism along a map of
bases.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The group `Z_r(X_s)` of `r`-cycles on the scheme-theoretic fibre of `f` at `s`. -/
abbrev fiberCycleGroup {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (r : ℕ) : Type u :=
  CycleGroup (f.fiber s) (f.fiberDimensionFunction s) r

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- The additive group of families of `r`-cycles on fibres of `f : X ⟶ S`. -/
abbrev familyOfCyclesOnFibres {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) : Type u :=
  (s : S) → f.fiberCycleGroup s r

end AlgebraicGeometry

namespace AlgebraicGeometry.FamilyOfCyclesOnFibres

/-- The identification `X'_{s'} ⟶ X_{g(s')}` of scheme-theoretic fibres induced by
the cartesian square of `f` along `g`. -/
noncomputable def fiberBaseChangeMap {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (s' : S') :
    (pullback.snd f g).fiber s' ⟶ f.fiber (g s') :=
  Scheme.Hom.baseChangeFiberMap f g (pullback.fst f g) (pullback.snd f g)
    (IsPullback.of_hasPullback f g) s'

/-- The degree-`r` cycle on `X'_{s'}` associated to the inverse image of the reduced
closure of a point of `X_{g(s')}`. -/
noncomputable def fiberBaseChangeOfPoint {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (x : f.fiber (g s')) :
    (pullback.snd f g).fiberCycleGroup s' r :=
  Scheme.IdealSheafData.associatedCycle
    ((Scheme.PointClosure.reducedStructure x).ideal.comap (fiberBaseChangeMap f g s'))
    ((pullback.snd f g).fiberDimensionFunction s') r

/-- The coefficient of fibrewise field-extension base change at a point of `X'_{s'}`. -/
noncomputable def fiberBaseChangeCoeff {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : f.fiberCycleGroup (g s') r) (x' : (pullback.snd f g).fiber s') : ℤ :=
  ∑ᶠ x : f.fiber (g s'),
    CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (g s')) r α x *
      (CycleGroup.toAlgebraicCycle ((pullback.snd f g).fiberDimensionFunction s') r
        (fiberBaseChangeOfPoint f g r s' x)) x'

/-- The coefficient function of fibrewise base change has locally finite support. -/
theorem fiberBaseChangeLocallyFiniteSupport {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : f.fiberCycleGroup (g s') r) :
    LocallyFiniteSupport (fiberBaseChangeCoeff f g r s' α) := sorry

/-- The underlying algebraic cycle of fibrewise field-extension base change. -/
noncomputable def fiberBaseChangeCycle {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : f.fiberCycleGroup (g s') r) :
    AlgebraicCycle ((pullback.snd f g).fiber s') ℤ where
  toFun := fiberBaseChangeCoeff f g r s' α
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x' _ ↦
    fiberBaseChangeLocallyFiniteSupport f g r s' α x'

/-- The underlying fibrewise base-change cycle is supported in dimension `r`. -/
theorem fiberBaseChangeCycle_mem_dimensionSubgroup {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : f.fiberCycleGroup (g s') r) :
    fiberBaseChangeCycle f g r s' α ∈
      AlgebraicCycle.dimensionSubgroup
        ((pullback.snd f g).fiberDimensionFunction s') r := sorry

/-- The underlying degree-`r` cycle of fibrewise field-extension base change. -/
noncomputable def fiberBaseChangeValue {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : f.fiberCycleGroup (g s') r) :
    (pullback.snd f g).fiberCycleGroup s' r :=
  ⟨fiberBaseChangeCycle f g r s' α,
    fiberBaseChangeCycle_mem_dimensionSubgroup f g r s' α⟩

/-- Fibrewise base change sends the zero cycle to zero. -/
theorem fiberBaseChangeValue_zero {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S') :
    fiberBaseChangeValue f g r s' 0 = 0 := sorry

/-- Fibrewise base change preserves addition of degree-`r` cycles. -/
theorem fiberBaseChangeValue_add {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (a b : f.fiberCycleGroup (g s') r) :
    fiberBaseChangeValue f g r s' (a + b) =
      fiberBaseChangeValue f g r s' a + fiberBaseChangeValue f g r s' b := sorry

/-- Fibrewise field-extension base change of `r`-cycles along `X'_{s'} ⟶ X_{g(s')}`. -/
noncomputable def fiberBaseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S') :
    f.fiberCycleGroup (g s') r →+ (pullback.snd f g).fiberCycleGroup s' r where
  toFun := fiberBaseChangeValue f g r s'
  map_zero' := fiberBaseChangeValue_zero f g r s'
  map_add' := fiberBaseChangeValue_add f g r s'

/-- Coefficients of fibrewise base change are given by `fiberBaseChangeCoeff`. -/
theorem fiberBaseChange_apply {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : f.fiberCycleGroup (g s') r) (x' : (pullback.snd f g).fiber s') :
    CycleGroup.toAlgebraicCycle ((pullback.snd f g).fiberDimensionFunction s') r
        (fiberBaseChange f g r s' α) x' =
      fiberBaseChangeCoeff f g r s' α x' := sorry

/-- The zero family is sent to the zero family. -/
theorem baseChange_zero {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) :
    (fun s' ↦ fiberBaseChange f g r s' 0) =
      (0 : familyOfCyclesOnFibres (pullback.snd f g) r) := sorry

/-- Base change of families preserves addition. -/
theorem baseChange_add {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (a b : familyOfCyclesOnFibres f r) :
    (fun s' ↦ fiberBaseChange f g r s' (a (g s') + b (g s'))) =
      (fun s' ↦ fiberBaseChange f g r s' (a (g s'))) +
        fun s' ↦ fiberBaseChange f g r s' (b (g s')) := sorry

/-- Base change of families of `r`-cycles on fibres along `g : S' ⟶ S`. -/
noncomputable def baseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) :
    familyOfCyclesOnFibres f r →+ familyOfCyclesOnFibres (pullback.snd f g) r where
  toFun α s' := fiberBaseChange f g r s' (α (g s'))
  map_zero' := baseChange_zero f g r
  map_add' := baseChange_add f g r

/-- Evaluation of family base change is fibrewise field-extension base change. -/
theorem baseChange_apply {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : familyOfCyclesOnFibres f r) (s' : S') :
    baseChange f g r α s' = fiberBaseChange f g r s' (α (g s')) := sorry

end AlgebraicGeometry.FamilyOfCyclesOnFibres
