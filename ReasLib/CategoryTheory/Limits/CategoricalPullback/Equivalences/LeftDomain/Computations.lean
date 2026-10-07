module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.LeftDomain.Basic

/-!
# Computations for left-domain maps of categorical pullbacks

Object and morphism formulas for left-domain change and its explicit inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory
namespace Limits.CategoricalPullback

section CategoricalPullbackEquivalencesImplementation

section CatPullbackMore

variable {A₀ B₀ D₀ : Type*} [Category A₀] [Category B₀] [Category D₀]

/-- Left-domain change applies `E` to the left endpoint object.

Proof strategy: project the explicit object formula of `DomainChange.Left.map`. -/
@[simp]
theorem DomainChange.Left.map.obj.fst
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : (E ⋙ F) ⊡ G) :
    ((DomainChange.Left.map E F G).obj x).fst = E.obj x.fst := sorry

/-- Left-domain change retains the right endpoint object.

Proof strategy: project the explicit object formula of `DomainChange.Left.map`. -/
@[simp]
theorem DomainChange.Left.map.obj.snd
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : (E ⋙ F) ⊡ G) :
    ((DomainChange.Left.map E F G).obj x).snd = x.snd := sorry

/-- Left-domain change retains the structural isomorphism.

Proof strategy: project the structural isomorphism of the explicit object formula of
`DomainChange.Left.map`. -/
@[simp]
theorem DomainChange.Left.map.obj.iso
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : (E ⋙ F) ⊡ G) :
    ((DomainChange.Left.map E F G).obj x).iso = x.iso := sorry

/-- Left-domain change applies `E` to the left component of a morphism.

Proof strategy: project the explicit morphism formula of `DomainChange.Left.map`. -/
@[simp]
theorem DomainChange.Left.map.hom.fst
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : (E ⋙ F) ⊡ G} (f : x ⟶ y) :
    ((DomainChange.Left.map E F G).map f).fst = E.map f.fst := sorry

/-- Left-domain change retains the right component of a morphism.

Proof strategy: project the explicit morphism formula of `DomainChange.Left.map`. -/
@[simp]
theorem DomainChange.Left.map.hom.snd
    {A₀' : Type*} [Category A₀'] (E : A₀' ⥤ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : (E ⋙ F) ⊡ G} (f : x ⟶ y) :
    ((DomainChange.Left.map E F G).map f).snd = f.snd := sorry

/-- Inverse left-domain change applies the inverse equivalence functor to the left endpoint. -/
@[simp]
theorem DomainChange.Left.inverse.obj.fst
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Left.inverse E F G).obj x).fst = E.inverse.obj x.fst := sorry

/-- Inverse left-domain change retains the right endpoint. -/
@[simp]
theorem DomainChange.Left.inverse.obj.snd
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Left.inverse E F G).obj x).snd = x.snd := sorry

/-- Inverse left-domain change transports the structural isomorphism by the counit of the
domain equivalence. -/
@[simp]
theorem DomainChange.Left.inverse.obj.iso
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀) (x : F ⊡ G) :
    ((DomainChange.Left.inverse E F G).obj x).iso =
      F.mapIso (E.counitIso.app x.fst) ≪≫ x.iso := sorry

/-- Inverse left-domain change applies the inverse equivalence functor to the left component of
a morphism. -/
@[simp]
theorem DomainChange.Left.inverse.hom.fst
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : F ⊡ G} (f : x ⟶ y) :
    ((DomainChange.Left.inverse E F G).map f).fst = E.inverse.map f.fst := sorry

/-- Inverse left-domain change retains the right component of a morphism. -/
@[simp]
theorem DomainChange.Left.inverse.hom.snd
    {A₀' : Type*} [Category A₀'] (E : A₀' ≌ A₀)
    (F : A₀ ⥤ D₀) (G : B₀ ⥤ D₀)
    {x y : F ⊡ G} (f : x ⟶ y) :
    ((DomainChange.Left.inverse E F G).map f).snd = f.snd := sorry

end CatPullbackMore

end CategoricalPullbackEquivalencesImplementation
end Limits.CategoricalPullback
end CategoryTheory
