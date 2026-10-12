/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Comparison.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudofunctor structure on relative inertia

This leaf assembles the pseudo-comma action on relative inertia into a
pseudofunctor.  The object, square, `2`-cell, and comparison data are owned by
the lower `Relative.Action` and `Relative.Comparison` layers; only the
pseudofunctor coherence belongs here.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia
namespace pseudoComma

noncomputable section

namespace pseudofunctorImplementation

/-- The prelax core of the pseudo-comma relative-inertia action, assembled from its public
object action and local hom functors. -/
private def prelax :
    PrelaxFunctor
      (Bicategory.PseudoComma
        (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
        (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
      (BasedCategory.{v₁, max u₁ v₁} C) :=
  PrelaxFunctor.mkOfHomFunctors
    (fun S ↦ relativeInertia S.hom)
    pseudoComma.mapFunctor

/-- The identity comparison of the pseudo-comma relative-inertia prelax core. -/
private def mapIdOwner
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))) :
    prelax.map (𝟙 S) ≅ 𝟙 (prelax.obj S) :=
  mapIdIso S

/-- The composition comparison of the pseudo-comma relative-inertia prelax core. -/
private def mapCompOwner
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) :
    prelax.map (f ≫ g) ≅ prelax.map f ≫ prelax.map g :=
  mapCompIso f g

/-- The pseudo-comma relative-inertia action preserves left whiskering up to its canonical
composition comparisons. -/
private theorem map₂_whisker_left
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) {g h : T ⟶ U} (η : g ⟶ h) :
    prelax.map₂ (f ◁ η) =
      (mapCompOwner f g).hom ≫
        prelax.map f ◁ prelax.map₂ η ≫
          (mapCompOwner f h).inv := sorry

/-- The pseudo-comma relative-inertia action preserves right whiskering up to its canonical
composition comparisons. -/
private theorem map₂_whisker_right
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    {f g : S ⟶ T} (η : f ⟶ g) (h : T ⟶ U) :
    prelax.map₂ (η ▷ h) =
      (mapCompOwner f h).hom ≫
        prelax.map₂ η ▷ prelax.map h ≫
          (mapCompOwner g h).inv := sorry

/-- The pseudo-comma relative-inertia action carries associators through its canonical
composition comparisons. -/
private theorem map₂_associator
    {R S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    prelax.map₂ (α_ f g h).hom =
      (mapCompOwner (f ≫ g) h).hom ≫
        (mapCompOwner f g).hom ▷ prelax.map h ≫
          (α_ (prelax.map f) (prelax.map g) (prelax.map h)).hom ≫
            prelax.map f ◁ (mapCompOwner g h).inv ≫
              (mapCompOwner f (g ≫ h)).inv := sorry

/-- The pseudo-comma relative-inertia action carries left unitors through its canonical
identity and composition comparisons. -/
private theorem map₂_left_unitor
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) :
    prelax.map₂ (λ_ f).hom =
      (mapCompOwner (𝟙 S) f).hom ≫
        (mapIdOwner S).hom ▷ prelax.map f ≫
          (λ_ (prelax.map f)).hom := sorry

/-- The pseudo-comma relative-inertia action carries right unitors through its canonical
identity and composition comparisons. -/
private theorem map₂_right_unitor
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) :
    prelax.map₂ (ρ_ f).hom =
      (mapCompOwner f (𝟙 T)).hom ≫
        prelax.map f ◁ (mapIdOwner T).hom ≫
          (ρ_ (prelax.map f)).hom := sorry

end pseudofunctorImplementation

variable (C) in
/-- Relative inertia is a universe-changing pseudofunctor on the pseudo comma bicategory of
the identity pseudofunctor on categories over `C`.

It sends an arrow over `C` to its relative inertia, an invertibly commuting square to the
induced square map, and a `2`-morphism of squares to its left-endpoint action on relative
inertia. -/
@[stacks 04Z4 "pseudofunctorial pseudo-comma relative inertia"]
noncomputable def pseudofunctor :
    Pseudofunctor
      (Bicategory.PseudoComma
        (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
        (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
      (BasedCategory.{v₁, max u₁ v₁} C) where
  toPrelaxFunctor := pseudofunctorImplementation.prelax
  mapId := pseudofunctorImplementation.mapIdOwner
  mapComp := pseudofunctorImplementation.mapCompOwner
  map₂_whisker_left := pseudofunctorImplementation.map₂_whisker_left
  map₂_whisker_right := pseudofunctorImplementation.map₂_whisker_right
  map₂_associator := pseudofunctorImplementation.map₂_associator
  map₂_left_unitor := pseudofunctorImplementation.map₂_left_unitor
  map₂_right_unitor := pseudofunctorImplementation.map₂_right_unitor

end

end pseudoComma
end RelativeInertia
end BasedCategory
end CategoryTheory
