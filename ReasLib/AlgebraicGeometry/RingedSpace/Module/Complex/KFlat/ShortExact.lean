/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.ShortExact
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-flat complexes on a ringed space

This leaf specializes the short-exact K-flatness owner to complexes of `𝒪_X`-modules.  The
termwise-flat API is canonical; the stalkwise-flat API is a source-facing bridge supplied by
`CochainComplex.isTermwiseFlat_iff`.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex.IsKFlat

variable {X : RingedSpace.{u}}
variable {S : ShortComplex (CochainComplex (Modules X) ℤ)}

/-- K-flatness of the third term from a short exact sequence and canonical termwise flatness. -/
@[stacks 0G6U "ringed-space K-flat short-exact owner (third term)"]
theorem obj₃_of_shortExact
    (hS : S.ShortExact)
    (hFlat₃ : HomologicalComplex.IsTermwiseFlat S.X₃)
    (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := sorry

/-- K-flatness of the middle term from a short exact sequence and canonical termwise flatness. -/
@[stacks 0G6U "ringed-space K-flat short-exact owner (middle term)"]
theorem obj₂_of_shortExact
    (hS : S.ShortExact)
    (hFlat₃ : HomologicalComplex.IsTermwiseFlat S.X₃)
    (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := sorry

/-- K-flatness of the first term from a short exact sequence and canonical termwise flatness. -/
@[stacks 0G6U "ringed-space K-flat short-exact owner (first term)"]
theorem obj₁_of_shortExact
    (hS : S.ShortExact)
    (hFlat₃ : HomologicalComplex.IsTermwiseFlat S.X₃)
    (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := sorry

/-- Source-facing bridge for the third-term clause of Lemma 20.26.7. -/
theorem obj₃_of_shortExact_of_flat
    (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n))
    (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := sorry

/-- Source-facing bridge for the middle-term clause of Lemma 20.26.7. -/
theorem obj₂_of_shortExact_of_flat
    (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n))
    (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := sorry

/-- Source-facing bridge for the first-term clause of Lemma 20.26.7. -/
theorem obj₁_of_shortExact_of_flat
    (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n))
    (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex.IsKFlat

end
