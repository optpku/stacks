/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Comparison.Composition.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition comparison computations for pseudo-comma relative inertia

This leaf exposes objectwise, underlying-arrow, and whiskering projections
of the canonical composition comparison.
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

/-- The underlying forward arrow of a composition comparison is the identity. -/
@[simp, stacks 04Z4 "relative-inertia composition comparison forward underlying arrow"]
theorem app.hom.underlying
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) (A : (relativeInertia S.hom).obj) :
    CategoryTheory.RelativeInertia.hom (app f g A).hom =
      𝟙 (((pseudoComma.map f ⋙ pseudoComma.map g).obj A).obj) := sorry

/-- The underlying inverse arrow of a composition comparison is the identity. -/
@[simp, stacks 04Z4 "relative-inertia composition comparison inverse underlying arrow"]
theorem app.inv.underlying
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) (A : (relativeInertia S.hom).obj) :
    CategoryTheory.RelativeInertia.hom (app f g A).inv =
      𝟙 (((pseudoComma.map f ⋙ pseudoComma.map g).obj A).obj) := sorry

end mapCompIso

namespace mapCompIso

/-- The forward component of the composition comparison is its objectwise comparison. -/
@[simp, stacks 04Z4 "relative-inertia composition comparison forward component"]
theorem hom.app
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) (A : (relativeInertia S.hom).obj) :
    (pseudoComma.mapCompIso f g).hom.toNatTrans.app A = (app f g A).hom := sorry

/-- The inverse component of the composition comparison is its inverse objectwise comparison. -/
@[simp, stacks 04Z4 "relative-inertia composition comparison inverse component"]
theorem inv.app
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) (A : (relativeInertia S.hom).obj) :
    (pseudoComma.mapCompIso f g).inv.toNatTrans.app A = (app f g A).inv := sorry

/-- Every forward component of the packaged pseudo-comma composition comparison is vertical over
the identity base arrow. -/
@[stacks 04Z4 "relative-inertia packaged composition comparison forward verticality"]
theorem hom.app.isHomLift
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) (A : (relativeInertia S.hom).obj) :
    (relativeInertia U.hom).p.IsHomLift
      (𝟙 ((relativeInertia S.hom).p.obj A))
      ((pseudoComma.mapCompIso f g).hom.toNatTrans.app A) := sorry

/-- Every inverse component of the packaged pseudo-comma composition comparison is vertical over
the identity base arrow. -/
@[stacks 04Z4 "relative-inertia packaged composition comparison inverse verticality"]
theorem inv.app.isHomLift
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) (g : T ⟶ U) (A : (relativeInertia S.hom).obj) :
    (relativeInertia U.hom).p.IsHomLift
      (𝟙 ((relativeInertia S.hom).p.obj A))
      ((pseudoComma.mapCompIso f g).inv.toNatTrans.app A) := sorry

end mapCompIso

/-- Relative inertia carries left whiskering through composition comparisons. -/
@[stacks 04Z4 "relative-inertia composition comparison left whiskering"]
theorem map₂.whiskerLeft
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    (f : S ⟶ T) {g h : T ⟶ U} (η : g ⟶ h) :
    pseudoComma.map₂ (f ◁ η) =
      (mapCompIso f g).hom ≫
        BasedCategory.whiskerLeft (pseudoComma.map f) (pseudoComma.map₂ η) ≫
          (mapCompIso f h).inv := sorry

/-- Relative inertia carries right whiskering through composition comparisons. -/
@[stacks 04Z4 "relative-inertia composition comparison right whiskering"]
theorem map₂.whiskerRight
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}
    {f g : S ⟶ T} (η : f ⟶ g) (h : T ⟶ U) :
    pseudoComma.map₂ (η ▷ h) =
      (mapCompIso f h).hom ≫
        BasedCategory.whiskerRight (pseudoComma.map₂ η) (pseudoComma.map h) ≫
          (mapCompIso g h).inv := sorry

end
end RelativeInertia.pseudoComma
end CategoryTheory.BasedCategory
