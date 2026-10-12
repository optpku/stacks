/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.FlatCompatibility
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

/-!
# Field-extension pullback of cycle groups

This file names cycles of fixed relative dimension over a field and the
canonical pullback along a field extension.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.FieldExtension

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The group `Z_r(X)` of cycles of relative dimension `r` on a scheme over a
field. -/
abbrev cycleGroup {k : Type u} [Field k] (X : SchemeOverField k) (r : ℕ) : Type u :=
  CycleGroup X.left (X.hom.relativeDimensionFunction
    (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))) (r : ℤ)

end AlgebraicGeometry.SchemeOverField

namespace AlgebraicGeometry.CycleGroup.FieldExtension

/-- Flat pullback of degree-`r` cycles along a field extension `K / k`. -/
noncomputable def algebraicExtensionPullback
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Algebraic X] (r : ℕ) :
    SchemeOverField.cycleGroup X r →+
      SchemeOverField.cycleGroup (Over.baseChange k K X) r :=
  (CycleGroup.reindex
      ((Over.baseChange k K X).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
      (add_zero (r : ℤ))).comp
    (CycleGroup.baseChangePullback (specMap k K)
      (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ)) 0
      (AlgebraicGeometry.Scheme.Hom.isDimensionFunctionCompatible_zero
        (specMap k K)) X.hom r)

/-- The algebraic-extension pullback of an `r`-cycle is the reindexed flat
base-change pullback along `Spec K ⟶ Spec k`. -/
theorem algebraicExtensionPullback_apply
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Algebraic X] (r : ℕ)
    (α : SchemeOverField.cycleGroup X r) :
    CycleGroup.toAlgebraicCycle
        ((Over.baseChange k K X).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        (r : ℤ) (algebraicExtensionPullback k K X r α) =
      CycleGroup.toAlgebraicCycle
        ((Over.baseChange k K X).hom.relativeDimensionFunction (fun _ ↦ (0 : ℤ)))
        ((r : ℤ) + 0)
        (CycleGroup.baseChangePullback (specMap k K)
          (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ)) 0
          (AlgebraicGeometry.Scheme.Hom.isDimensionFunctionCompatible_zero
            (specMap k K)) X.hom r α) :=
  sorry

/-- Field-extension pullback of `r`-cycles is injective. -/
theorem algebraicExtensionPullback_injective
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : SchemeOverField k) [Algebraic X] (r : ℕ) :
    Function.Injective (algebraicExtensionPullback k K X r) :=
  sorry

end AlgebraicGeometry.CycleGroup.FieldExtension
