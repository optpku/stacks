/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.BaseChange
public import ReasLib.AlgebraicGeometry.RelativeCycle.Functoriality
public import ReasLib.AlgebraicGeometry.RelativeCycle.ClosedImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Base change of an effective relative `r`-cycle remains effective. -/
theorem effectiveBaseChange_mem {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) (α : effective f r) :
    FamilyOfCyclesOnFibres.baseChange f g r (α : f.FiberCycleFamily r) ∈ effective (pullback.snd f g) r :=
  sorry

/-- Base change of effective relative `r`-cycles along `g : S' ⟶ S`. -/
def effectiveBaseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) : effective f r →+ effective (pullback.snd f g) r :=
  ((FamilyOfCyclesOnFibres.baseChange f g r).restrict (effective f r)).codRestrict
    (effective (pullback.snd f g) r) (effectiveBaseChange_mem f g r)

/-- The underlying fibrewise family of `effectiveBaseChange` is family-level
base change. -/
theorem effectiveBaseChange_apply {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) (α : effective f r) :
    (effectiveBaseChange f g r α : (pullback.snd f g).FiberCycleFamily r) =
      FamilyOfCyclesOnFibres.baseChange f g r (α : f.FiberCycleFamily r) :=
  rfl

/-- Membership of a base-changed effective cycle in `z^{eff}(X'/S', r)`. -/
theorem mem_effectiveBaseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [IsLocallyNoetherian S] [IsLocallyNoetherian S'] [LocallyOfFiniteType f]
    (r : ℕ) (α : effective f r) :
    (effectiveBaseChange f g r α : (pullback.snd f g).FiberCycleFamily r) ∈
      effective (pullback.snd f g) r :=
  (effectiveBaseChange f g r α).property

/-- An isomorphism over a common base pushes forward fibrewise cycle families additively. -/
def familyMapOfIsoOver {X X' S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {f' : X' ⟶ S} [LocallyOfFiniteType f'] (e : X ⟶ X') [IsIso e]
    (w : e ≫ f' = f) (r : ℕ) : f.FiberCycleFamily r →+ f'.FiberCycleFamily r :=
  AddMonoidHom.pi fun s : S ↦
    (CycleGroup.mapHom (pushforwardFiberMap f f' e w s)
      (f.fiberDimensionFunction s) (f'.fiberDimensionFunction s) r).comp
        (Pi.evalAddMonoidHom
          (fun t : S ↦ CycleGroup (f.fiber t) (f.fiberDimensionFunction t) r) s)

/-- Isomorphism transport evaluates as pushforward along the induced fibre morphism. -/
theorem familyMapOfIsoOver_apply {X X' S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {f' : X' ⟶ S} [LocallyOfFiniteType f']
    (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (r : ℕ)
    (α : f.FiberCycleFamily r) (s : S) :
    familyMapOfIsoOver e w r α s =
      CycleGroup.mapHom (pushforwardFiberMap f f' e w s)
        (f.fiberDimensionFunction s) (f'.fiberDimensionFunction s) r (α s) := rfl

/-- Transport of effective relative cycles along an isomorphism of morphisms over
a common base remains effective. -/
theorem effectiveMapOfIsoOver_mem {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (r : ℕ) (α : effective f r) :
    familyMapOfIsoOver e w r (α : f.FiberCycleFamily r) ∈ effective f' r :=
  sorry

/-- Transport of effective relative cycles along an isomorphism of morphisms over
a common base. -/
def effectiveMapOfIsoOver {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (e : X ⟶ X') [IsIso e] (w : e ≫ f' = f) (r : ℕ) :
    effective f r →+ effective f' r :=
  ((familyMapOfIsoOver e w r).restrict (effective f r)).codRestrict
    (effective f' r) (effectiveMapOfIsoOver_mem e w r)

end AlgebraicGeometry.RelativeCycle
