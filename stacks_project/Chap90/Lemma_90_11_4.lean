/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.LinearLift
import StacksCheckRecall

/-!
# Lemma 90.11.4

A finite-product-preserving functor from finitely generated `R`-modules, or from
all `R`-modules, to types, sending `0` to a singleton, lifts uniquely to an
`R`-linear functor landing in `ModuleCat R` whose composite with the forgetful
functor recovers the original functor.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe u v

variable {R : Type u} [CommRing R]

/- Lemma 90.11.4 (1): a functor `L : FGModuleCat R ⥤ Type` with `L.obj 0` a singleton
that preserves finite products lifts uniquely to an `R`-linear functor
`FGModuleCat R ⥤ ModuleCat R` whose composite with `forget` is `L`. -/
@[stacks 06I6] #check (FGModuleCat.existsUnique_linearLift (R := R) :
  ∀ (L : FGModuleCat.{v} R ⥤ Type v),
    ∀ [PreservesFiniteProducts L] [Unique (L.obj 0)],
      ∃! F : FGModuleCat.{v} R ⥤ ModuleCat.{v} R,
        F.ModuleLinear R ∧ F ⋙ forget (ModuleCat.{v} R) = L)

/- Lemma 90.11.4 (2): a functor `L : ModuleCat R ⥤ Type` with `L.obj 0` a singleton
that preserves finite products lifts uniquely to an `R`-linear functor
`ModuleCat R ⥤ ModuleCat R` whose composite with `forget` is `L`. -/
@[stacks 06I6] #check (ModuleCat.existsUnique_linearLift (R := R) :
  ∀ (L : ModuleCat.{v} R ⥤ Type v),
    ∀ [PreservesFiniteProducts L] [Unique (L.obj 0)],
      ∃! F : ModuleCat.{v} R ⥤ ModuleCat.{v} R,
        F.ModuleLinear R ∧ F ⋙ forget (ModuleCat.{v} R) = L)
