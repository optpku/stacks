/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Map.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity comparison construction for based inertia

This leaf owns the objectwise identity comparison and the proof data needed to
assemble its based natural isomorphism.  Component readouts live in
`Comparison.Identity.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

namespace Inertia
namespace mapIdIso

/-- The identity underlying arrow intertwines the two relative-inertia automorphisms in the
identity comparison for based inertia. -/
private theorem appComm
    (S : BasedCategory.{v₁, u₁} C) (A : (inertia S).obj) :
    ((Inertia.map (𝟭 S)).toFunctor.obj A).aut.hom ≫ 𝟙 A.obj =
      𝟙 A.obj ≫ A.aut.hom := sorry

/-- The objectwise identity comparison for based inertia. Its underlying total-category
isomorphism is the identity. -/
@[stacks 04Z4 "based inertia identity-comparison component"]
def app
    (S : BasedCategory.{v₁, u₁} C) (A : (inertia S).obj) :
    (Inertia.map (𝟭 S)).obj A ≅ A :=
  CategoryTheory.RelativeInertia.isoMk S.p (Iso.refl _)
    (appComm S A)

/-- The objectwise identity comparisons for based inertia are natural in inertia morphisms. -/
@[reassoc, stacks 04Z4 "based inertia identity-comparison naturality"]
theorem app.naturality
    (S : BasedCategory.{v₁, u₁} C)
    {A B : (inertia S).obj} (f : A ⟶ B) :
    (Inertia.map (𝟭 S)).map f ≫ (app S B).hom =
      (app S A).hom ≫ f := sorry

/-- Every forward identity-comparison component for based inertia is vertical over the
identity base map. -/
@[stacks 04Z4 "based inertia identity-comparison hom-lift"]
theorem app.isHomLift
    (S : BasedCategory.{v₁, u₁} C) (A : (inertia S).obj) :
    (inertia S).p.IsHomLift
      (𝟙 ((inertia S).p.obj A))
      (app S A).hom := sorry

/-- Every inverse identity-comparison component for based inertia is vertical over the
identity base map. -/
@[stacks 04Z4 "based inertia inverse identity-comparison hom-lift"]
theorem app.inv.isHomLift
    (S : BasedCategory.{v₁, u₁} C) (A : (inertia S).obj) :
    (inertia S).p.IsHomLift
      (𝟙 ((inertia S).p.obj A))
      (app S A).inv := sorry

end mapIdIso

/-- The canonical componentwise based natural isomorphism witnessing identity preservation by
based inertia. -/
@[stacks 04Z4 "based identity comparison"]
def mapIdIso (S : BasedCategory.{v₁, u₁} C) :
    Inertia.map (𝟭 S) ≅ 𝟭 (inertia S) :=
  BasedNatIso.ofComponents
    (mapIdIso.app S)
    (fun f ↦ mapIdIso.app.naturality S f)
    (mapIdIso.app.isHomLift S)

end Inertia

end BasedCategory
end CategoryTheory
