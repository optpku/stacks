module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map.Basic

/-!
# Two-cell action on categorical pullback maps

This module owns the natural transformation and natural isomorphism induced by morphisms and
isomorphisms of cospan transformations.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]

namespace Limits.CategoricalPullback

variable {H : X ⥤ Z} {I : Y ⥤ Z} {F : A ⥤ C} {G : B ⥤ C}

/-- A morphism of cospan transformations induces a natural transformation between the
corresponding pullback maps. -/
def mapNatTrans {ψ ψ' : CatCospanTransform H I F G} (η : ψ ⟶ ψ') :
    map ψ ⟶ map ψ' :=
  mapFunctor.map η

/-- The left component of the natural transformation induced on pullback maps. -/
@[simp]
theorem mapNatTrans.app.fst {ψ ψ' : CatCospanTransform H I F G}
    (η : ψ ⟶ ψ') (P : H ⊡ I) :
    ((mapNatTrans η).app P).fst = η.left.app P.fst := sorry

/-- The right component of the natural transformation induced on pullback maps. -/
@[simp]
theorem mapNatTrans.app.snd {ψ ψ' : CatCospanTransform H I F G}
    (η : ψ ⟶ ψ') (P : H ⊡ I) :
    ((mapNatTrans η).app P).snd = η.right.app P.snd := sorry

/-- An isomorphism of cospan transformations induces a natural isomorphism between the
corresponding pullback maps. -/
def mapNatIso {ψ ψ' : CatCospanTransform H I F G} (e : ψ ≅ ψ') :
    map ψ ≅ map ψ' :=
  mapFunctor.mapIso e

/-- The left component of the forward map of the natural isomorphism induced on pullback
maps. -/
@[simp]
theorem mapNatIso.hom.app.fst {ψ ψ' : CatCospanTransform H I F G}
    (e : ψ ≅ ψ') (P : H ⊡ I) :
    ((mapNatIso e).hom.app P).fst = e.hom.left.app P.fst := sorry

/-- The right component of the forward map of the natural isomorphism induced on pullback
maps. -/
@[simp]
theorem mapNatIso.hom.app.snd {ψ ψ' : CatCospanTransform H I F G}
    (e : ψ ≅ ψ') (P : H ⊡ I) :
    ((mapNatIso e).hom.app P).snd = e.hom.right.app P.snd := sorry

/-- The left component of the inverse map of the natural isomorphism induced on pullback
maps. -/
@[simp]
theorem mapNatIso.inv.app.fst {ψ ψ' : CatCospanTransform H I F G}
    (e : ψ ≅ ψ') (P : H ⊡ I) :
    ((mapNatIso e).inv.app P).fst = e.inv.left.app P.fst := sorry

/-- The right component of the inverse map of the natural isomorphism induced on pullback
maps. -/
@[simp]
theorem mapNatIso.inv.app.snd {ψ ψ' : CatCospanTransform H I F G}
    (e : ψ ≅ ψ') (P : H ⊡ I) :
    ((mapNatIso e).inv.app P).snd = e.inv.right.app P.snd := sorry

end Limits.CategoricalPullback

end CategoryTheory

/- Axiom audit: the two-cell action is induced by the functorial map owner. -/
