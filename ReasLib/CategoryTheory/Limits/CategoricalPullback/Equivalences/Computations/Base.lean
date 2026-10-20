/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.Base

/-!
# Structural computations for common-base transport

Forward and inverse comparison maps for transporting a categorical pullback along an equivalence
of the common base.
-/

@[expose] public section

namespace CategoryTheory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
namespace Limits.CategoricalPullback
section EquivalenceTransportComputations
variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]
/-- The structural forward map of inverse common-base change is the unit-conjugated
inverse-base image of the original comparison. -/
@[simp]
theorem BaseChange.inverse.obj.iso.hom
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀')
    (x : (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor)) :
    ((BaseChange.inverse F G eB).obj x).iso.hom =
      eB.unitIso.hom.app (F.obj x.fst) ≫
        eB.inverse.map x.iso.hom ≫
          eB.unitIso.inv.app (G.obj x.snd) := sorry

/-- The structural inverse map of inverse common-base change is the reverse
unit-conjugated inverse-base image of the original comparison. -/
@[simp]
theorem BaseChange.inverse.obj.iso.inv
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {D₀' : Type*} [Category D₀'] (eB : D₀ ≌ D₀')
    (x : (F ⋙ eB.functor) ⊡ (G ⋙ eB.functor)) :
    ((BaseChange.inverse F G eB).obj x).iso.inv =
      eB.unitIso.hom.app (G.obj x.snd) ≫
        eB.inverse.map x.iso.inv ≫
          eB.unitIso.inv.app (F.obj x.fst) := sorry


end EquivalenceTransportComputations
end Limits.CategoricalPullback
end CategoryTheory
