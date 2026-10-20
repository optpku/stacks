/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.LeftDomain.Basic

/-!
# Structural computations for left-domain transport

Comparison-map formulas for precomposing the left cospan leg, including the explicit inverse
associated to a domain equivalence.
-/

@[expose] public section

namespace CategoryTheory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
namespace Limits.CategoricalPullback
section EquivalenceTransportComputations
variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]
/-- Left-domain transport preserves the forward structural comparison map. -/
@[simp]
theorem DomainChange.Left.map.obj.iso.hom
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : (E ⋙ F) ⊡ G) :
    ((DomainChange.Left.map E F G).obj x).iso.hom = x.iso.hom := sorry

/-- Left-domain transport preserves the inverse structural comparison map. -/
@[simp]
theorem DomainChange.Left.map.obj.iso.inv
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : (E ⋙ F) ⊡ G) :
    ((DomainChange.Left.map E F G).obj x).iso.inv = x.iso.inv := sorry

/-- The forward structural comparison map of inverse left-domain transport is the image of the
domain-equivalence counit followed by the original comparison. -/
@[simp]
theorem DomainChange.Left.inverse.obj.iso.hom
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Left.inverse E F G).obj x).iso.hom =
      F.map (E.counitIso.hom.app x.fst) ≫ x.iso.hom := sorry

/-- The inverse structural comparison map of inverse left-domain transport is the original
comparison inverse followed by the image of the inverse domain-equivalence counit. -/
@[simp]
theorem DomainChange.Left.inverse.obj.iso.inv
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Left.inverse E F G).obj x).iso.inv =
      x.iso.inv ≫ F.map (E.counitIso.inv.app x.fst) := sorry


end EquivalenceTransportComputations
end Limits.CategoricalPullback
end CategoryTheory
