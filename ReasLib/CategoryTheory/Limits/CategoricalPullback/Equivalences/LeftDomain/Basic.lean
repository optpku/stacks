/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.MapProperties

/-!
# Left-domain maps of categorical pullbacks

Precomposition of the left cospan leg, its induced categorical-pullback map, and the canonical
property-transfer instances. Explicit inverse and equivalence data live in later leaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory
namespace Limits.CategoricalPullback

section CategoricalPullbackEquivalencesImplementation

section CatPullbackMore

variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]

/-- Precomposition of the left pullback leg as a categorical cospan transformation. -/
def DomainChange.Left.transform
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    CatCospanTransform (E ⋙ F) G F G :=
  CatCospanTransform.ofIso
    (Functor.rightUnitor (E ⋙ F))
    (Functor.rightUnitor G ≪≫ (Functor.leftUnitor G).symm)

/-- The inverse cospan transformation to left-domain change along an equivalence. Its left square
is obtained from the counit of the domain equivalence. -/
def DomainChange.Left.inverseTransform
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    CatCospanTransform F G (E.functor ⋙ F) G :=
  CatCospanTransform.ofIso
    (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm ≪≫
      Functor.isoWhiskerRight E.counitIso.symm F ≪≫
        Functor.associator E.inverse E.functor F)
    (Functor.rightUnitor G ≪≫ (Functor.leftUnitor G).symm)

/-- Precompose the left leg with a functor `E` on its domain. -/
noncomputable def DomainChange.Left.map {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) : (E ⋙ F) ⊡ G ⥤ F ⊡ G :=
  CategoricalPullback.map (DomainChange.Left.transform E F G)

/-- The explicit inverse to left-domain change along an equivalence. -/
noncomputable def DomainChange.Left.inverse
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    F ⊡ G ⥤ (E.functor ⋙ F) ⊡ G :=
  CategoricalPullback.map (DomainChange.Left.inverseTransform E F G)

namespace DomainChange.Left.map

/-- Left-domain transport is faithful when the changing-domain functor is faithful.

This owner-specialized instance exposes `CategoricalPullback.map.faithful` without asking
typeclass search to unfold `DomainChange.Left.map`. -/
instance faithful
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) [E.Faithful] :
    (DomainChange.Left.map E F G).Faithful := sorry

/-- Left-domain transport is full when the changing-domain functor is full.

This owner-specialized instance exposes `CategoricalPullback.map.full`. -/
instance full
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) [E.Full] :
    (DomainChange.Left.map E F G).Full := sorry

/-- Left-domain transport is essentially surjective when the changing-domain functor is.

This owner-specialized instance exposes `CategoricalPullback.map.essSurj`. -/
instance essSurj
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) [E.EssSurj] :
    (DomainChange.Left.map E F G).EssSurj := sorry

/-- Left-domain transport is an equivalence when the changing-domain functor is fully faithful
and essentially surjective.

This owner-specialized instance exposes `CategoricalPullback.map.isEquivalence`. -/
instance isEquivalence
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) [E.Full] [E.Faithful] [E.EssSurj] :
    (DomainChange.Left.map E F G).IsEquivalence := sorry

end DomainChange.Left.map

end CatPullbackMore

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback
end CategoryTheory

section LeftDomainChangeInstanceSmoke

open CategoryTheory

universe v u

variable {A A' B D : Type u}
variable [Category.{v} A] [Category.{v} A'] [Category.{v} B] [Category.{v} D]
variable (E : A' ≌ A) (F : A ⥤ D) (G : B ⥤ D)

#synth (CategoryTheory.Limits.CategoricalPullback.DomainChange.Left.map E.functor F G).Faithful
#synth (CategoryTheory.Limits.CategoricalPullback.DomainChange.Left.map E.functor F G).Full
#synth (CategoryTheory.Limits.CategoricalPullback.DomainChange.Left.map E.functor F G).EssSurj
#synth (CategoryTheory.Limits.CategoricalPullback.DomainChange.Left.map E.functor F G).IsEquivalence

end LeftDomainChangeInstanceSmoke
