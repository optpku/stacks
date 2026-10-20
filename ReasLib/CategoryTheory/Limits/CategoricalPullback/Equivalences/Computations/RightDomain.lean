/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.RightDomain.Basic

/-!
# Structural computations for right-domain transport

Comparison-map formulas for precomposing the right cospan leg, including the explicit inverse
associated to a domain equivalence.
-/

@[expose] public section

namespace CategoryTheory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
namespace Limits.CategoricalPullback
section EquivalenceTransportComputations
variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]
/-- Right-domain transport preserves the forward structural comparison map. -/
@[simp]
theorem DomainChange.Right.map.obj.iso.hom
    {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ (E ⋙ G)) :
    ((DomainChange.Right.map E F G).obj x).iso.hom = x.iso.hom := sorry

/-- Right-domain transport preserves the inverse structural comparison map. -/
@[simp]
theorem DomainChange.Right.map.obj.iso.inv
    {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ (E ⋙ G)) :
    ((DomainChange.Right.map E F G).obj x).iso.inv = x.iso.inv := sorry

/-- The forward structural comparison map of inverse right-domain transport is the original
comparison followed by the image of the inverse domain-equivalence counit. -/
@[simp]
theorem DomainChange.Right.inverse.obj.iso.hom
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Right.inverse E F G).obj x).iso.hom =
      x.iso.hom ≫ G.map (E.counitIso.inv.app x.snd) := sorry

/-- The inverse structural comparison map of inverse right-domain transport is the image of the
domain-equivalence counit followed by the original comparison inverse. -/
@[simp]
theorem DomainChange.Right.inverse.obj.iso.inv
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Right.inverse E F G).obj x).iso.inv =
      G.map (E.counitIso.hom.app x.snd) ≫ x.iso.inv := sorry

end EquivalenceTransportComputations
end Limits.CategoricalPullback
end CategoryTheory
