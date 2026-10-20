/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

open Scheme.Hom

namespace ChowGroup

/-- The additive transport from Chow classes on an iterated base change to Chow classes on
the base change along the composite, including transport of the grading index. -/
noncomputable def iteratedBaseChangeMap
    {S S' S'' X : Scheme.{u}} [UniversallyCatenary S'']
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (g' : S'' ⟶ S')
    (δ'' : S'' → ℤ) [IsDimensionFunction δ''] {a b : ℤ} (h : a = b) :
    ChowGroup (pullback (pullback.snd f g) g')
        ((pullback.snd (pullback.snd f g) g').relativeDimensionFunction δ'') a →+
      ChowGroup (pullback f (g' ≫ g))
        ((pullback.snd f (g' ≫ g)).relativeDimensionFunction δ'') b :=
  (reindex ((pullback.snd f (g' ≫ g)).relativeDimensionFunction δ'') h).toAddMonoidHom.comp
    (@map S'' inferInstance δ'' inferInstance
      (Over.mk (pullback.snd (pullback.snd f g) g'))
      (Over.mk (pullback.snd f (g' ≫ g)))
      (inferInstance : LocallyOfFiniteType (pullback.snd (pullback.snd f g) g'))
      (inferInstance : LocallyOfFiniteType (pullback.snd f (g' ≫ g)))
      ((Over.pullbackComp g' g).app (Over.mk f)).inv inferInstance a)

/-- Transport across the canonical pullback-composition isomorphism commutes with passage
from cycles to Chow classes. -/
theorem iteratedBaseChangeMap_chowClass
    {S S' S'' X : Scheme.{u}} [UniversallyCatenary S'']
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (g' : S'' ⟶ S')
    (δ'' : S'' → ℤ) [IsDimensionFunction δ''] {a b : ℤ} (h : a = b)
    (α : CycleGroup (pullback (pullback.snd f g) g')
      ((pullback.snd (pullback.snd f g) g').relativeDimensionFunction δ'') a) :
    iteratedBaseChangeMap f g g' δ'' h
        (chowClass
          ((pullback.snd (pullback.snd f g) g').relativeDimensionFunction δ'') a α) =
      chowClass ((pullback.snd f (g' ≫ g)).relativeDimensionFunction δ'') b
        (CycleGroup.iteratedBaseChangeMap f g g' δ'' h α) := sorry

/-- Successive dimension-shifted flat-base-change pullbacks on Chow groups equal pullback
along the composite after the canonical pullback and grading transports. -/
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

end ChowGroup

end AlgebraicGeometry
