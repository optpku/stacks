/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.LocalizationAway
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module-level localization-away vanishing

This leaf records the ordinary-module consequence of the derived localization-away predicate.
The predicate itself is owned by `Completeness.LocalizationAway`; this file adds the reusable
linear-map subsingleton bridge used by principal-adic arguments.

@stack 091R
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace ModuleCat

variable {A : Type u} [CommRing A]

/--
Lemma 15.92.3 (Stacks `091R`): the ordinary-module multiplication tower whose
`n`-th object is `M` and whose transition map is multiplication by `f`.

The carrier and maps are exposed explicitly so adic-completion arguments can
reuse the same inverse system without rebuilding local definitions.
-/
@[stacks 091R "the module multiplication tower"]
abbrev localizationAwayModuleTower (f : A) (M : ModuleCat.{max u v, u} A) :
    CategoryTheory.SequentialInverseSystem (ModuleCat.{max u v, u} A) :=
  Functor.ofOpSequence (X := fun _ ↦ M) (fun _ ↦ f • 𝟙 M)

/-- Lemma 15.92.3 (Stacks `091R`): module localization-away vanishing makes maps from `A_f`
to `M` subsingleton. -/
@[stacks 091R "linear-map subsingleton from localization-away vanishing"]
theorem moduleLocalizationAwayTVanishing.linearMap_subsingleton
    {M : ModuleCat.{max u v, u} A} {f : A}
    (h : moduleLocalizationAwayTVanishing M f) :
    Subsingleton (Localization.Away f →ₗ[A] M) := sorry

end ModuleCat
