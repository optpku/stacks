/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Base change of families of cycles on fibres

Base change is defined fibrewise by pulling back reduced point closures and
taking their associated cycles, with multiplicities extended additively.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FamilyOfCyclesOnFibres

/-- The degree-`r` cycle associated to the inverse image of a reduced point
closure under the canonical morphism between base-changed fibres. -/
noncomputable def fiberBaseChangeOfPoint {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (x : f.fiber (g s')) :
    CycleGroup ((pullback.snd f g).fiber s')
      ((pullback.snd f g).fiberRelativeDimensionFunction s') r :=
  @Scheme.IdealSheafData.associatedCycle ((pullback.snd f g).fiber s')
    (@instIsLocallyNoetherianPullbackSchemeOfLocallyOfFiniteType _ _ _
      (pullback.snd f g) (S'.fromSpecResidueField s')
      (instUniversallyCatenarySpecResidueField s').toIsLocallyNoetherian inferInstance)
    ((Scheme.PointClosure.reducedStructure x).ideal.comap
      (Scheme.Hom.baseChangeFiberMap f g (pullback.fst f g) (pullback.snd f g)
        (IsPullback.of_hasPullback f g) s'))
    ((pullback.snd f g).fiberRelativeDimensionFunction s') r

/-- The base-change coefficient at a point is the sum of the original
coefficients times the multiplicities of the pulled-back reduced point closures. -/
noncomputable def fiberBaseChangeCoeff {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r)
    (x' : (pullback.snd f g).fiber s') : ℤ :=
  ∑ᶠ x : f.fiber (g s'),
    CycleGroup.toAlgebraicCycle (f.fiberRelativeDimensionFunction (g s')) r α x *
      (CycleGroup.toAlgebraicCycle ((pullback.snd f g).fiberRelativeDimensionFunction s') r
        (fiberBaseChangeOfPoint f g r s' x)) x'

/-- The coefficient function of fibrewise base change has locally finite support. -/
theorem fiberBaseChangeLocallyFiniteSupport {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r) :
    LocallyFiniteSupport (fiberBaseChangeCoeff f g r s' α) := sorry

/-- The algebraic cycle with the coefficients of fibrewise field-extension base change. -/
noncomputable def fiberBaseChangeCycle {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r) :
    AlgebraicCycle ((pullback.snd f g).fiber s') ℤ where
  toFun := fiberBaseChangeCoeff f g r s' α
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x' _ ↦
    fiberBaseChangeLocallyFiniteSupport f g r s' α x'

/-- The fibrewise base-change cycle is supported in dimension `r`. -/
theorem fiberBaseChangeCycle_mem_dimensionSubgroup {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r) :
    fiberBaseChangeCycle f g r s' α ∈
      AlgebraicCycle.dimensionSubgroup
        ((pullback.snd f g).fiberRelativeDimensionFunction s') r := sorry

/-- The degree-`r` cycle obtained by fibrewise field-extension base change. -/
noncomputable def fiberBaseChangeValue {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r) :
    CycleGroup ((pullback.snd f g).fiber s')
      ((pullback.snd f g).fiberRelativeDimensionFunction s') r :=
  ⟨fiberBaseChangeCycle f g r s' α,
    fiberBaseChangeCycle_mem_dimensionSubgroup f g r s' α⟩

/-- Fibrewise base change sends the zero cycle to zero. -/
theorem fiberBaseChangeValue_zero {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S') :
    fiberBaseChangeValue f g r s' 0 = 0 := sorry

/-- Fibrewise base change preserves addition of degree-`r` cycles. -/
theorem fiberBaseChangeValue_add {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (a b : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r) :
    fiberBaseChangeValue f g r s' (a + b) =
      fiberBaseChangeValue f g r s' a + fiberBaseChangeValue f g r s' b := sorry

/-- The additive homomorphism of degree-`r` cycles induced by field extension
along the canonical morphism between base-changed fibres. -/
noncomputable def fiberBaseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S') :
    CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r →+
      CycleGroup ((pullback.snd f g).fiber s')
        ((pullback.snd f g).fiberRelativeDimensionFunction s') r where
  toFun := fiberBaseChangeValue f g r s'
  map_zero' := fiberBaseChangeValue_zero f g r s'
  map_add' := fiberBaseChangeValue_add f g r s'

/-- Coefficients of the fibrewise base-change homomorphism are given by
the sum of coefficients times pulled-back point-closure multiplicities. -/
theorem fiberBaseChange_apply {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (s' : S')
    (α : CycleGroup (f.fiber (g s')) (f.fiberRelativeDimensionFunction (g s')) r)
    (x' : (pullback.snd f g).fiber s') :
    CycleGroup.toAlgebraicCycle ((pullback.snd f g).fiberRelativeDimensionFunction s') r
        (fiberBaseChange f g r s' α) x' =
      fiberBaseChangeCoeff f g r s' α x' := sorry

/-- The additive homomorphism of families of degree-`r` fibre cycles induced
by a morphism of bases. -/
noncomputable def baseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ) :
    f.FiberCycleFamily r →+ (pullback.snd f g).FiberCycleFamily r :=
  AddMonoidHom.pi fun s' ↦ (fiberBaseChange f g r s').comp
    (Pi.evalAddMonoidHom
      (fun s ↦ CycleGroup (f.fiber s) (f.fiberRelativeDimensionFunction s) r) (g s'))

/-- Evaluation of family base change is fibrewise field-extension base change. -/
theorem baseChange_apply {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : f.FiberCycleFamily r) (s' : S') :
    baseChange f g r α s' = fiberBaseChange f g r s' (α (g s')) := sorry

/-- Base change along a point-bijective morphism inducing residue-field
isomorphisms is bijective on families of nonnegative-dimensional fibre cycles
of a locally finite type morphism. -/
theorem baseChange_bijective {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (hg : Function.Bijective g) (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ) :
    Function.Bijective (baseChange f g r) := sorry

end AlgebraicGeometry.FamilyOfCyclesOnFibres
