/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import ReasLib.Algebra.Homology.CochainComplex.KFlat
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat complexes in short exact sequences on a ringed site

For a short exact sequence of cochain complexes, termwise flatness of the cokernel makes
K-flatness a two-out-of-three property.  The termwise-flat hypothesis uses the generic
`HomologicalComplex.IsTermwiseFlat` owner explicitly; it is not a typeclass.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.CochainComplex.IsKFlat

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable {S : ShortComplex (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)}

/-- Lemma 21.17.7 (1): if the first two complexes in a short exact sequence are K-flat and the
third is termwise flat, then the third complex is K-flat. -/
@[stacks 0G7B "(1)"]
theorem obj₃_of_shortExact
    (hS : S.ShortExact) (hFlat₃ : HomologicalComplex.IsTermwiseFlat S.X₃)
    (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := sorry

/-- Lemma 21.17.7 (2): if the outer complexes in a short exact sequence are K-flat and the third
is termwise flat, then the middle complex is K-flat. -/
@[stacks 0G7B "(2)"]
theorem obj₂_of_shortExact
    (hS : S.ShortExact) (hFlat₃ : HomologicalComplex.IsTermwiseFlat S.X₃)
    (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := sorry

/-- Lemma 21.17.7 (3): if the last two complexes in a short exact sequence are K-flat and the
third is termwise flat, then the first complex is K-flat. -/
@[stacks 0G7B "(3)"]
theorem obj₁_of_shortExact
    (hS : S.ShortExact) (hFlat₃ : HomologicalComplex.IsTermwiseFlat S.X₃)
    (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := sorry

end

end SheafOfModules.RingedSite.CochainComplex.IsKFlat
