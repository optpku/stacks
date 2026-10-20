module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Action.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition comparison construction for pseudo-comma relative inertia

This leaf owns the objectwise composition comparison and the proof data
needed to assemble its based natural isomorphism.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v u₁ v₁

namespace CategoryTheory.BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia.pseudoComma

noncomputable section

namespace mapCompIso

/-- The composite-square and iterated-square automorphisms are intertwined by the identity arrow. -/
private theorem appComm
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) (A : (relativeInertia S.hom).obj) :
    ((pseudoComma.map (f ≫ g)).toFunctor.obj A).aut.hom ≫
        𝟙 (((pseudoComma.map f ⋙ pseudoComma.map g).obj A).obj) =
      𝟙 (((pseudoComma.map f ⋙ pseudoComma.map g).obj A).obj) ≫
        ((pseudoComma.map f ⋙ pseudoComma.map g).toFunctor.obj A).aut.hom := sorry

/-- The objectwise composition comparison for the pseudo-comma relative-inertia action. -/
@[stacks 04Z4 "relative-inertia composition comparison component"]
def app
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) (A : (relativeInertia S.hom).obj) :
    (pseudoComma.map (f ≫ g)).obj A ≅
      (pseudoComma.map f ⋙ pseudoComma.map g).obj A :=
  CategoryTheory.RelativeInertia.isoMk
    ((Bicategory.ColaxComma.hom U).toFunctor :
      (Bicategory.ColaxComma.left U).obj ⥤
        (Bicategory.ColaxComma.right U).obj)
    (Iso.refl _) (appComm f g A)

/-- The objectwise composition comparisons are natural in relative-inertia morphisms. -/
@[reassoc, stacks 04Z4 "relative-inertia composition comparison naturality"]
theorem app.naturality
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U)
    {A B : (relativeInertia S.hom).obj} (φ : A ⟶ B) :
    (pseudoComma.map (f ≫ g)).toFunctor.map φ ≫ (app f g B).hom =
      (app f g A).hom ≫
        (pseudoComma.map f ⋙ pseudoComma.map g).toFunctor.map φ := sorry

/-- Every objectwise composition-comparison component is vertical over the identity base arrow. -/
@[stacks 04Z4 "relative-inertia composition comparison forward verticality"]
theorem app.isHomLift
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) (A : (relativeInertia S.hom).obj) :
    (relativeInertia U.hom).p.IsHomLift
      (𝟙 ((relativeInertia S.hom).p.obj A)) (app f g A).hom := sorry

/-- Every inverse objectwise composition-comparison component is vertical over the identity base
arrow. -/
@[stacks 04Z4 "relative-inertia composition comparison inverse verticality"]
theorem app.inv.isHomLift
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) (A : (relativeInertia S.hom).obj) :
    (relativeInertia U.hom).p.IsHomLift
      (𝟙 ((relativeInertia S.hom).p.obj A)) (app f g A).inv := sorry

end mapCompIso

/-- The canonical based natural isomorphism witnessing composition preservation by the
pseudo-comma relative-inertia action. -/
@[stacks 04Z4 "pseudo-comma composition comparison"]
def mapCompIso
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) :
    pseudoComma.map (f ≫ g) ≅ pseudoComma.map f ⋙ pseudoComma.map g :=
  BasedNatIso.ofComponents (mapCompIso.app f g)
    (fun φ ↦ mapCompIso.app.naturality f g φ)
    (mapCompIso.app.isHomLift f g)

end
end RelativeInertia.pseudoComma
end CategoryTheory.BasedCategory
