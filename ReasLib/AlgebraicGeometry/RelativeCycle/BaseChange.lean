/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

/-!
# Base change of relative cycles

Base change along a scheme morphism acts on relative cycles, and universal
homeomorphisms with residue-field isomorphisms induce bijections on them.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Base change of a relative `r`-cycle along a morphism of locally Noetherian
bases remains a relative `r`-cycle. -/
theorem groupBaseChange_mem {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) (α : group f r) :
    FamilyOfCyclesOnFibres.baseChange f g r (α : f.FiberCycleFamily r) ∈
      group (pullback.snd f g) r := sorry

/-- Base change of relative `r`-cycles along `g : S' ⟶ S`. -/
noncomputable def groupBaseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) : group f r →+ group (pullback.snd f g) r :=
  ((FamilyOfCyclesOnFibres.baseChange f g r).restrict (group f r)).codRestrict
    (group (pullback.snd f g) r) (groupBaseChange_mem f g r)

/-- The underlying fibrewise family of `groupBaseChange` is family-level base change. -/
theorem groupBaseChange_apply {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) (α : group f r) :
    (groupBaseChange f g r α : (pullback.snd f g).FiberCycleFamily r) =
      FamilyOfCyclesOnFibres.baseChange f g r (α : f.FiberCycleFamily r) := rfl

/-- A fibrewise family is relative if and only if its base change along a
universal homeomorphism inducing residue-field isomorphisms is relative. -/
theorem isRelative_iff_baseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    [UniversalHomeomorphism g] (hκ : ∀ s', IsIso (g.residueFieldMap s'))
    {r : ℕ} {α : f.FiberCycleFamily r} :
    IsRelative α ↔
      IsRelative (FamilyOfCyclesOnFibres.baseChange f g r α) := sorry

/-- The explicit family inverse preserves relative cycles. -/
theorem isRelative_baseChangeInverse {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    [UniversalHomeomorphism g] (hg : Function.Bijective g)
    (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ)
    (α : (pullback.snd f g).FiberCycleFamily r) (hα : IsRelative α) :
    IsRelative (FamilyOfCyclesOnFibres.baseChangeInverse f g hg hκ r α) := by
  apply (isRelative_iff_baseChange f g hκ).mpr
  simpa only [FamilyOfCyclesOnFibres.baseChange_baseChangeInverse] using hα

/-- Base change with its explicit coefficient inverse, restricted to relative cycles. -/
def groupBaseChangeEquiv {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    [UniversalHomeomorphism g]
    (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ) :
    group f r ≃+ group (pullback.snd f g) r where
  toFun := groupBaseChange f g r
  invFun α := ⟨FamilyOfCyclesOnFibres.baseChangeInverse f g g.isHomeomorph.bijective hκ r α.1,
    isRelative_baseChangeInverse f g g.isHomeomorph.bijective hκ r α.1 α.2⟩
  left_inv α := Subtype.ext
    (FamilyOfCyclesOnFibres.baseChangeInverse_baseChange f g g.isHomeomorph.bijective hκ r α.1)
  right_inv α := Subtype.ext
    (FamilyOfCyclesOnFibres.baseChange_baseChangeInverse f g g.isHomeomorph.bijective hκ r α.1)
  map_add' := (groupBaseChange f g r).map_add


/-- If `g : S' ⟶ S` is a universal homeomorphism of locally Noetherian schemes
inducing residue-field isomorphisms, base change bijects the relative `r`-cycle
groups of a locally finite type morphism `f : X ⟶ S` and its pullback. -/
theorem groupBaseChange_bijective {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    [UniversalHomeomorphism g] (hκ : ∀ s', IsIso (g.residueFieldMap s')) (r : ℕ) :
    Function.Bijective (groupBaseChange f g r) :=
  (groupBaseChangeEquiv f g hκ r).bijective

end AlgebraicGeometry.RelativeCycle
