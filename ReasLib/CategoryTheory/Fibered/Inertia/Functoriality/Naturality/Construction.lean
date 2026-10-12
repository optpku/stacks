/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.ToInertia.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of relative-to-absolute inertia naturality

This leaf owns the canonical based natural isomorphism comparing relative-inertia mapping with
passage to absolute inertia.  Objectwise and component readouts are layered separately.
-/

@[expose] public section

universe u v u₁ v₁ u₁' v₁' u₂ v₂ u₂' v₂'

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]
variable
    {S₁ : BasedCategory.{v₁, u₁} C} {S₁' : BasedCategory.{v₁', u₁'} C}
    {S₂ : BasedCategory.{v₂, u₂} C} {S₂' : BasedCategory.{v₂', u₂'} C}
    {F₁ : S₁ ⥤ᵇ S₁'} {F₂ : S₂ ⥤ᵇ S₂'}

namespace RelativeInertia.toInertia

namespace Implementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The identity arrow satisfies the forward component equation. -/
private theorem componentHomComm
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : CategoryTheory.RelativeInertia F₁.toFunctor) :
    ((RelativeInertia.map G G' comm ⋙ RelativeInertia.toInertia F₂).obj X).aut.hom ≫
        𝟙 _ =
      𝟙 _ ≫
        ((RelativeInertia.toInertia F₁ ⋙ Inertia.map G).obj X).aut.hom := sorry

end Implementation

namespace naturalityIso

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The objectwise isomorphism in relative-to-absolute inertia naturality. Both directions
have identity underlying arrows. -/
@[stacks 04Z5 "objectwise based naturality of relative-to-absolute inertia"]
def component
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : CategoryTheory.RelativeInertia F₁.toFunctor) :
    (RelativeInertia.map G G' comm ⋙ RelativeInertia.toInertia F₂).obj X ≅
      (RelativeInertia.toInertia F₁ ⋙ Inertia.map G).obj X :=
  CategoryTheory.RelativeInertia.isoMk S₂.p (Iso.refl _)
    (Implementation.componentHomComm G G' comm X)

end naturalityIso

namespace naturalityIso

/-- The forward objectwise comparison is natural in relative-inertia morphisms. -/
@[reassoc, stacks 04Z5 "relative-to-absolute inertia naturality"]
theorem naturality
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    {X Y : CategoryTheory.RelativeInertia F₁.toFunctor} (f : X ⟶ Y) :
    (RelativeInertia.map G G' comm ⋙ RelativeInertia.toInertia F₂).map f ≫
        (naturalityIso.component G G' comm Y).hom =
      (naturalityIso.component G G' comm X).hom ≫
        (RelativeInertia.toInertia F₁ ⋙ Inertia.map G).map f := sorry

/-- The inverse objectwise comparison is natural in relative-inertia morphisms. -/
@[reassoc, stacks 04Z5 "relative-to-absolute inertia inverse naturality"]
theorem invNaturality
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    {X Y : CategoryTheory.RelativeInertia F₁.toFunctor} (f : X ⟶ Y) :
    (naturalityIso.component G G' comm X).inv ≫
        (RelativeInertia.map G G' comm ⋙ RelativeInertia.toInertia F₂).map f =
      (RelativeInertia.toInertia F₁ ⋙ Inertia.map G).map f ≫
        (naturalityIso.component G G' comm Y).inv := sorry

/-- Every forward component is vertical over the identity of the base. -/
@[stacks 04Z5 "relative-to-absolute inertia forward component verticality"]
theorem component.hom.isHomLift
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : CategoryTheory.RelativeInertia F₁.toFunctor) :
    (inertia S₂).p.IsHomLift
      (𝟙 ((relativeInertia F₁).p.obj X))
      (naturalityIso.component G G' comm X).hom := sorry

/-- Every inverse component is vertical over the identity of the base. -/
@[stacks 04Z5 "relative-to-absolute inertia inverse component verticality"]
theorem component.inv.isHomLift
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂)
    (X : CategoryTheory.RelativeInertia F₁.toFunctor) :
    (inertia S₂).p.IsHomLift
      (𝟙 ((relativeInertia F₁).p.obj X))
      (naturalityIso.component G G' comm X).inv := sorry

end naturalityIso

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The canonical comparison from relative to absolute inertia is natural for invertibly
commuting squares in `Cat/C`. -/
@[stacks 04Z5 "based naturality of relative-to-absolute inertia"]
def naturalityIso
    (G : S₁ ⥤ᵇ S₂) (G' : S₁' ⥤ᵇ S₂')
    (comm : F₁ ⋙ G' ≅ G ⋙ F₂) :
    RelativeInertia.map G G' comm ⋙ RelativeInertia.toInertia F₂ ≅
      RelativeInertia.toInertia F₁ ⋙ Inertia.map G :=
  BasedNatIso.ofComponents
    (naturalityIso.component G G' comm)
    (fun {_ _} f ↦ naturalityIso.naturality G G' comm f)
    (naturalityIso.component.hom.isHomLift G G' comm)

end RelativeInertia.toInertia

end BasedCategory
end CategoryTheory
