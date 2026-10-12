/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition comparison construction for based inertia

This leaf owns the objectwise composition comparison and the proof data
needed to assemble its based natural isomorphism.  Component readouts live in
`Comparison.Composition.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v u₁ v₁ v₂ u₂ v₃ u₃

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]
variable
    {S₁ : BasedCategory.{v₁, u₁} C} {S₂ : BasedCategory.{v₂, u₂} C}

namespace Inertia
namespace mapCompIso

/-- The identity underlying arrow intertwines the two relative-inertia automorphisms in the
composition comparison for based inertia. -/
private theorem appComm
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃) (A : (inertia S₁).obj) :
    ((Inertia.map (G ⋙ H)).toFunctor.obj A).aut.hom ≫
        𝟙 (((Inertia.map G ⋙ Inertia.map H).obj A).obj) =
      𝟙 (((Inertia.map G ⋙ Inertia.map H).obj A).obj) ≫
        ((Inertia.map G ⋙ Inertia.map H).toFunctor.obj A).aut.hom := sorry

/-- The objectwise composition comparison for based inertia. Its underlying total-category
isomorphism is the identity between the two explicit composite images. -/
@[stacks 04Z4 "based inertia composition-comparison component"]
def app
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃) (A : (inertia S₁).obj) :
    (Inertia.map (G ⋙ H)).obj A ≅
      (Inertia.map G ⋙ Inertia.map H).obj A :=
  CategoryTheory.RelativeInertia.isoMk S₃.p (Iso.refl _)
    (appComm G H A)

/-- The objectwise composition comparisons for based inertia are natural in inertia
morphisms. -/
@[reassoc, stacks 04Z4 "based inertia composition-comparison naturality"]
theorem app.naturality
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃)
    {A B : (inertia S₁).obj} (f : A ⟶ B) :
    (Inertia.map (G ⋙ H)).map f ≫ (app G H B).hom =
      (app G H A).hom ≫
        (Inertia.map G ⋙ Inertia.map H).map f := sorry

/-- Every forward composition-comparison component for based inertia is vertical over the
identity base map. -/
@[stacks 04Z4 "based inertia composition-comparison hom-lift"]
theorem app.isHomLift
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃) (A : (inertia S₁).obj) :
    (inertia S₃).p.IsHomLift
      (𝟙 ((inertia S₁).p.obj A))
      (app G H A).hom := sorry

/-- Every inverse composition-comparison component for based inertia is vertical over the
identity base map. -/
@[stacks 04Z4 "based inertia composition-comparison inverse hom-lift"]
theorem app.inv.isHomLift
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃) (A : (inertia S₁).obj) :
    (inertia S₃).p.IsHomLift
      (𝟙 ((inertia S₁).p.obj A))
      (app G H A).inv := sorry

end mapCompIso

/-- The canonical componentwise based natural isomorphism witnessing composition preservation
by based inertia. -/
@[stacks 04Z4 "based composition comparison"]
def mapCompIso
    {S₃ : BasedCategory.{v₃, u₃} C}
    (G : S₁ ⥤ᵇ S₂) (H : S₂ ⥤ᵇ S₃) :
    Inertia.map (G ⋙ H) ≅ Inertia.map G ⋙ Inertia.map H :=
  BasedNatIso.ofComponents
    (mapCompIso.app G H)
    (fun f ↦ mapCompIso.app.naturality G H f)
    (mapCompIso.app.isHomLift G H)

end Inertia

end BasedCategory
end CategoryTheory
