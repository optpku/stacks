/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Effective
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

open Scheme.Hom

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.IsEffective.flatPullback :
  ∀ {X' X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} {α : CyclesOnFibers f r} (hα : α.IsEffective)
    (h : X' ⟶ X) (e : ℕ) [Flat h] [RelativeDimension h e],
    CyclesOnFibers.IsEffective (Scheme.Hom.FiberCycleFamily.flatPullback h rfl e α))

/- Lemma 62.8.5: Let `f : X ⟶ S` be a morphism of schemes. Assume `S` locally
Noetherian and `f` locally of finite type. Let `r, e ≥ 0` be integers. Let `α`
be a relative `r`-cycle on `X / S`. Let `{f_i : X_i ⟶ X}` be a jointly
surjective family of flat morphisms, locally of finite type, and of relative
dimension `e`. Then `α` is effective if and only if each flat pullback
`f_i^* α` is effective. -/
@[stacks 0H5V]
#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.isEffective_iff_forall_flatPullback :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r e : ℕ) {ι : Type u}
    (family : ι → Over X) [∀ i, Flat (family i).hom]
    [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α),
    α.IsEffective ↔
      ∀ i, CyclesOnFibers.IsEffective
        (Scheme.Hom.FiberCycleFamily.flatPullback (family i).hom rfl e α))

#check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.isEffective_of_forall_flatPullback :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r e : ℕ) {ι : Type u}
    (family : ι → Over X) [∀ i, Flat (family i).hom]
    [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α)
    (h_eff : ∀ i,
      CyclesOnFibers.IsEffective
        (Scheme.Hom.FiberCycleFamily.flatPullback (family i).hom rfl e α)),
    α.IsEffective)

end AlgebraicGeometry
