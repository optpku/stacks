/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.RightDomain.Equivalence.Construction

/-!
# Computations for right-domain equivalence transport

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

/-- The inverse retained by `DomainChange.Right.quasiInverse` is explicit inverse right-domain change. -/
@[simp] theorem DomainChange.Right.quasiInverse.inverse
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Right.quasiInverse E F G).inverse = DomainChange.Right.inverse E F G := sorry

/-- The forward functor projection of right-domain congruence. -/
@[simp] theorem DomainChange.Right.equivalence.functor
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Right.equivalence E F G).functor = DomainChange.Right.map E.functor F G := sorry

/-- The inverse functor projection of right-domain congruence. -/
@[simp] theorem DomainChange.Right.equivalence.inverse
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Right.equivalence E F G).inverse = DomainChange.Right.inverse E F G := sorry

/-- The counit projection of right-domain congruence. -/
@[simp] theorem DomainChange.Right.equivalence.counitIso
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Right.equivalence E F G).counitIso =
      (DomainChange.Right.transformQuasiInverse E F G).mapCounitIso := sorry

/-- The unit projection of right-domain congruence. -/
theorem DomainChange.Right.equivalence.unitIso
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    (DomainChange.Right.equivalence E F G).unitIso =
      Equivalence.adjointifyη (DomainChange.Right.transformQuasiInverse E F G).mapUnitIso
        (DomainChange.Right.transformQuasiInverse E F G).mapCounitIso := sorry

/-- Unit hom left component computation. -/
@[simp] theorem DomainChange.Right.equivalence.unitIso.hom.app.fst
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : F ⊡ (E.functor ⋙ G)) :
    ((DomainChange.Right.equivalence E F G).unitIso.hom.app x).fst = 𝟙 x.fst := sorry
/-- Unit hom right component computation. -/
@[simp] theorem DomainChange.Right.equivalence.unitIso.hom.app.snd
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : F ⊡ (E.functor ⋙ G)) :
    ((DomainChange.Right.equivalence E F G).unitIso.hom.app x).snd = E.unitIso.hom.app x.snd := sorry
/-- Unit inverse left component computation. -/
@[simp] theorem DomainChange.Right.equivalence.unitIso.inv.app.fst
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : F ⊡ (E.functor ⋙ G)) :
    ((DomainChange.Right.equivalence E F G).unitIso.inv.app x).fst = 𝟙 x.fst := sorry
/-- Unit inverse right component computation. -/
@[simp] theorem DomainChange.Right.equivalence.unitIso.inv.app.snd
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : F ⊡ (E.functor ⋙ G)) :
    ((DomainChange.Right.equivalence E F G).unitIso.inv.app x).snd = E.unitIso.inv.app x.snd := sorry
/-- Counit hom left component computation. -/
@[simp] theorem DomainChange.Right.equivalence.counitIso.hom.app.fst
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : F ⊡ G) :
    ((DomainChange.Right.equivalence E F G).counitIso.hom.app x).fst = 𝟙 x.fst := sorry
/-- Counit hom right component computation. -/
@[simp] theorem DomainChange.Right.equivalence.counitIso.hom.app.snd
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : F ⊡ G) :
    ((DomainChange.Right.equivalence E F G).counitIso.hom.app x).snd = E.counitIso.hom.app x.snd := sorry
/-- Counit inverse left component computation. -/
@[simp] theorem DomainChange.Right.equivalence.counitIso.inv.app.fst
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : F ⊡ G) :
    ((DomainChange.Right.equivalence E F G).counitIso.inv.app x).fst = 𝟙 x.fst := sorry
/-- Counit inverse right component computation. -/
@[simp] theorem DomainChange.Right.equivalence.counitIso.inv.app.snd
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀) (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    (x : F ⊡ G) :
    ((DomainChange.Right.equivalence E F G).counitIso.inv.app x).snd = E.counitIso.inv.app x.snd := sorry

end CatPullbackMore

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback
end CategoryTheory
