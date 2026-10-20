/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Action.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity comparison construction for pseudo-comma relative inertia

This leaf owns the objectwise identity comparison and the proof data needed
to assemble its based natural isomorphism.
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

namespace mapIdIso

/-- The identity map of a pseudo-comma object induces an automorphism-compatible identity arrow
on every relative-inertia object. -/
private theorem appComm
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : (relativeInertia S.hom).obj) :
    ((pseudoComma.map (𝟙 S)).toFunctor.obj A).aut.hom ≫ 𝟙 A.obj =
      𝟙 A.obj ≫ A.aut.hom := sorry

/-- The objectwise identity comparison for the pseudo-comma relative-inertia action. Its
underlying total-category isomorphism is the identity. -/
@[stacks 04Z4 "relative-inertia identity comparison component"]
def app
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : (relativeInertia S.hom).obj) :
    (pseudoComma.map (𝟙 S)).obj A ≅ A :=
  CategoryTheory.RelativeInertia.isoMk
    ((Bicategory.ColaxComma.hom S).toFunctor :
      (Bicategory.ColaxComma.left S).obj ⥤
        (Bicategory.ColaxComma.right S).obj)
    (Iso.refl _) (appComm S A)

/-- The objectwise identity comparisons are natural in relative-inertia morphisms. -/
@[reassoc, stacks 04Z4 "relative-inertia identity comparison naturality"]
theorem app.naturality
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    {A B : (relativeInertia S.hom).obj} (φ : A ⟶ B) :
    (pseudoComma.map (𝟙 S)).toFunctor.map φ ≫ (app S B).hom =
      (app S A).hom ≫ φ := sorry

/-- Every objectwise identity-comparison component is vertical over the identity base arrow. -/
@[stacks 04Z4 "relative-inertia identity comparison forward verticality"]
theorem app.isHomLift
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : (relativeInertia S.hom).obj) :
    (relativeInertia S.hom).p.IsHomLift
      (𝟙 ((relativeInertia S.hom).p.obj A)) (app S A).hom := sorry

/-- Every inverse objectwise identity-comparison component is vertical over the identity base
arrow. -/
@[stacks 04Z4 "relative-inertia identity comparison inverse verticality"]
theorem app.inv.isHomLift
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : (relativeInertia S.hom).obj) :
    (relativeInertia S.hom).p.IsHomLift
      (𝟙 ((relativeInertia S.hom).p.obj A)) (app S A).inv := sorry

end mapIdIso

/-- The canonical based natural isomorphism witnessing identity preservation by the
pseudo-comma relative-inertia action. -/
@[stacks 04Z4 "pseudo-comma identity comparison"]
def mapIdIso
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))) :
    pseudoComma.map (𝟙 S) ≅ 𝟭 (relativeInertia S.hom) :=
  BasedNatIso.ofComponents (mapIdIso.app S)
    (fun φ ↦ mapIdIso.app.naturality S φ)
    (mapIdIso.app.isHomLift S)

end
end RelativeInertia.pseudoComma
end CategoryTheory.BasedCategory
