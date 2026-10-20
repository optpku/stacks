/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.FlatCompatibility.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

open Scheme.Hom

namespace CycleGroup

/-- The additive transport from cycles on an iterated base change to cycles on the base
change along the composite, including transport of the grading index. -/
noncomputable def iteratedBaseChangeMap
    {S S' S'' X : Scheme.{u}} [UniversallyCatenary S'']
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (g' : S'' ⟶ S')
    (δ'' : S'' → ℤ) [IsDimensionFunction δ''] {a b : ℤ} (h : a = b) :
    CycleGroup (pullback (pullback.snd f g) g')
        ((pullback.snd (pullback.snd f g) g').relativeDimensionFunction δ'') a →+
      CycleGroup (pullback f (g' ≫ g))
        ((pullback.snd f (g' ≫ g)).relativeDimensionFunction δ'') b :=
  (reindex ((pullback.snd f (g' ≫ g)).relativeDimensionFunction δ'') h).comp
    (mapHom ((Over.pullbackComp g' g).inv.app (Over.mk f)).left
      ((pullback.snd (pullback.snd f g) g').relativeDimensionFunction δ'')
      ((pullback.snd f (g' ≫ g)).relativeDimensionFunction δ'') a)

/-- On underlying algebraic cycles, transport across iterated base change is pushforward
along the inverse component of the canonical pullback-composition isomorphism. -/
theorem toAlgebraicCycle_iteratedBaseChangeMap
    {S S' S'' X : Scheme.{u}} [UniversallyCatenary S'']
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (g' : S'' ⟶ S')
    (δ'' : S'' → ℤ) [IsDimensionFunction δ''] {a b : ℤ} (h : a = b)
    (α : CycleGroup (pullback (pullback.snd f g) g')
      ((pullback.snd (pullback.snd f g) g').relativeDimensionFunction δ'') a) :
    toAlgebraicCycle ((pullback.snd f (g' ≫ g)).relativeDimensionFunction δ'') b
        (iteratedBaseChangeMap f g g' δ'' h α) =
      AlgebraicCycle.map ((Over.pullbackComp g' g).inv.app (Over.mk f)).left
        ((pullback.snd (pullback.snd f g) g').relativeDimensionFunction δ'')
        ((pullback.snd f (g' ≫ g)).relativeDimensionFunction δ'')
        (toAlgebraicCycle
          ((pullback.snd (pullback.snd f g) g').relativeDimensionFunction δ'') a α) := sorry

/-- Successive dimension-shifted flat-base-change pullbacks on cycles equal pullback along
the composite after the canonical pullback and grading transports. -/
theorem baseChangePullback_comp
    {S S' S'' X : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S'] [UniversallyCatenary S'']
    (g : S' ⟶ S) [Flat g] (g' : S'' ⟶ S') [Flat g']
    (δ : S → ℤ) [IsDimensionFunction δ] (δ' : S' → ℤ) [IsDimensionFunction δ']
    (δ'' : S'' → ℤ) [IsDimensionFunction δ''] (c c' : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (hcompat' : g'.IsDimensionFunctionCompatible δ' δ'' c')
    (f : X ⟶ S) [LocallyOfFiniteType f] (k : ℤ) :
    (iteratedBaseChangeMap f g g' δ'' (add_assoc k c c')).comp
        ((baseChangePullback g' δ' δ'' c' hcompat' (pullback.snd f g) (k + c)).comp
          (baseChangePullback g δ δ' c hcompat f k)) =
      baseChangePullback (g' ≫ g) δ δ'' (c + c')
        (IsDimensionFunctionCompatible.comp
          g g' δ δ' δ'' c c' hcompat hcompat') f k := sorry

end CycleGroup

end AlgebraicGeometry
