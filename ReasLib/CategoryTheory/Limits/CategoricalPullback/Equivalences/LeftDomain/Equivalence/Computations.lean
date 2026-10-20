/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.LeftDomain.Equivalence.Construction

/-!
# Computations for left-domain equivalence transport

This leaf contains projections and component formulas for the equivalence owner. The coherence
cells and deterministic quasi-inverse data remain in `Construction`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory
namespace Limits.CategoricalPullback

section CategoricalPullbackEquivalencesImplementation

section CatPullbackMore

variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]

/-- The inverse retained by `DomainChange.Left.quasiInverse` is explicit inverse left-domain change. -/
@[simp] theorem DomainChange.Left.quasiInverse.inverse
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Left.quasiInverse E F G).inverse = DomainChange.Left.inverse E F G := sorry

/-- The forward functor projection of left-domain congruence. -/
@[simp] theorem DomainChange.Left.equivalence.functor
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Left.equivalence E F G).functor = DomainChange.Left.map E.functor F G := sorry

/-- The inverse functor projection of left-domain congruence. -/
@[simp] theorem DomainChange.Left.equivalence.inverse
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Left.equivalence E F G).inverse = DomainChange.Left.inverse E F G := sorry

/-- The counit projection of left-domain congruence. -/
@[simp] theorem DomainChange.Left.equivalence.counitIso
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Left.equivalence E F G).counitIso =
      (DomainChange.Left.transformQuasiInverse E F G).mapCounitIso := sorry

/-- The unit projection of left-domain congruence. -/
theorem DomainChange.Left.equivalence.unitIso
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Left.equivalence E F G).unitIso =
      Equivalence.adjointifyη (DomainChange.Left.transformQuasiInverse E F G).mapUnitIso
        (DomainChange.Left.transformQuasiInverse E F G).mapCounitIso := sorry

/-- Unit hom left component computation. -/
@[simp] theorem DomainChange.Left.equivalence.unitIso.hom.app.fst
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : (E.functor ⋙ F) ⊡ G) :
    ((DomainChange.Left.equivalence E F G).unitIso.hom.app x).fst = E.unitIso.hom.app x.fst := sorry

/-- Unit hom right component computation. -/
@[simp] theorem DomainChange.Left.equivalence.unitIso.hom.app.snd
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : (E.functor ⋙ F) ⊡ G) :
    ((DomainChange.Left.equivalence E F G).unitIso.hom.app x).snd = 𝟙 x.snd := sorry

/-- Unit inverse left component computation. -/
@[simp] theorem DomainChange.Left.equivalence.unitIso.inv.app.fst
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : (E.functor ⋙ F) ⊡ G) :
    ((DomainChange.Left.equivalence E F G).unitIso.inv.app x).fst = E.unitIso.inv.app x.fst := sorry

/-- Unit inverse right component computation. -/
@[simp] theorem DomainChange.Left.equivalence.unitIso.inv.app.snd
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : (E.functor ⋙ F) ⊡ G) :
    ((DomainChange.Left.equivalence E F G).unitIso.inv.app x).snd = 𝟙 x.snd := sorry

/-- Counit hom left component computation. -/
@[simp] theorem DomainChange.Left.equivalence.counitIso.hom.app.fst
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : F ⊡ G) :
    ((DomainChange.Left.equivalence E F G).counitIso.hom.app x).fst = E.counitIso.hom.app x.fst := sorry

/-- Counit hom right component computation. -/
@[simp] theorem DomainChange.Left.equivalence.counitIso.hom.app.snd
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : F ⊡ G) :
    ((DomainChange.Left.equivalence E F G).counitIso.hom.app x).snd = 𝟙 x.snd := sorry

/-- Counit inverse left component computation. -/
@[simp] theorem DomainChange.Left.equivalence.counitIso.inv.app.fst
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : F ⊡ G) :
    ((DomainChange.Left.equivalence E F G).counitIso.inv.app x).fst = E.counitIso.inv.app x.fst := sorry

/-- Counit inverse right component computation. -/
@[simp] theorem DomainChange.Left.equivalence.counitIso.inv.app.snd
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : F ⊡ G) :
    ((DomainChange.Left.equivalence E F G).counitIso.inv.app x).snd = 𝟙 x.snd := sorry

end CatPullbackMore

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback
end CategoryTheory
