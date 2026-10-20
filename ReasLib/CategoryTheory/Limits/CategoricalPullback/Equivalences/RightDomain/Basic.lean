module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.MapProperties

/-!
# Right-domain maps of categorical pullbacks

Precomposition of the right cospan leg, its induced categorical-pullback map, and the canonical
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

/-- Precomposition of the right pullback leg as a categorical cospan transformation. -/
def DomainChange.Right.transform
    {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
  CatCospanTransform F (E ⋙ G) F G :=
  CatCospanTransform.ofIso
    (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)
    (Functor.rightUnitor (E ⋙ G))

/-- The inverse cospan transformation to right-domain change along an equivalence. Its right
square is obtained from the counit of the domain equivalence. -/
def DomainChange.Right.inverseTransform
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    CatCospanTransform F G F (E.functor ⋙ G) :=
  CatCospanTransform.ofIso
    (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)
    (Functor.rightUnitor G ≪≫ (Functor.leftUnitor G).symm ≪≫
      Functor.isoWhiskerRight E.counitIso.symm G ≪≫
        Functor.associator E.inverse E.functor G)

/-- Precompose the right leg with a functor `E` on its domain. -/
noncomputable def DomainChange.Right.map {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) : F ⊡ (E ⋙ G) ⥤ F ⊡ G :=
  CategoricalPullback.map (DomainChange.Right.transform E F G)

/-- The explicit inverse to right-domain change along an equivalence. -/
noncomputable def DomainChange.Right.inverse
    {B₀' : Type*} [Category B₀'] (E : B₀' ≌ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) :
    F ⊡ G ⥤ F ⊡ (E.functor ⋙ G) :=
  CategoricalPullback.map (DomainChange.Right.inverseTransform E F G)

namespace DomainChange.Right.map

/-- Right-domain transport is faithful when the changing-domain functor is faithful.

This owner-specialized instance exposes `CategoricalPullback.map.faithful` without asking
typeclass search to unfold `DomainChange.Right.map`. -/
instance faithful
    {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) [E.Faithful] :
    (DomainChange.Right.map E F G).Faithful := sorry

/-- Right-domain transport is full when the changing-domain functor is full.

This owner-specialized instance exposes `CategoricalPullback.map.full`. -/
instance full
    {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) [E.Full] :
    (DomainChange.Right.map E F G).Full := sorry

/-- Right-domain transport is essentially surjective when the changing-domain functor is.

This owner-specialized instance exposes `CategoricalPullback.map.essSurj`. -/
instance essSurj
    {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) [E.EssSurj] :
    (DomainChange.Right.map E F G).EssSurj := sorry

/-- Right-domain transport is an equivalence when the changing-domain functor is fully faithful
and essentially surjective.

This owner-specialized instance exposes `CategoricalPullback.map.isEquivalence`. -/
instance isEquivalence
    {B₀' : Type*} [Category B₀'] (E : B₀' ⥤ B₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) [E.Full] [E.Faithful] [E.EssSurj] :
    (DomainChange.Right.map E F G).IsEquivalence := sorry

end DomainChange.Right.map

end CatPullbackMore

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback
end CategoryTheory

section RightDomainChangeInstanceSmoke

open CategoryTheory

universe v u

variable {A B B' D : Type u}
variable [Category.{v} A] [Category.{v} B] [Category.{v} B'] [Category.{v} D]
variable (E : B' ≌ B) (F : A ⥤ D) (G : B ⥤ D)

#synth (CategoryTheory.Limits.CategoricalPullback.DomainChange.Right.map E.functor F G).Faithful
#synth (CategoryTheory.Limits.CategoricalPullback.DomainChange.Right.map E.functor F G).Full
#synth (CategoryTheory.Limits.CategoricalPullback.DomainChange.Right.map E.functor F G).EssSurj
#synth (CategoryTheory.Limits.CategoricalPullback.DomainChange.Right.map E.functor F G).IsEquivalence

end RightDomainChangeInstanceSmoke
