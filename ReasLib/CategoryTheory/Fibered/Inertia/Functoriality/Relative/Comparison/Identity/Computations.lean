/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Comparison.Identity.Construction

import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity comparison computations for pseudo-comma relative inertia

This leaf exposes the objectwise and underlying-arrow projections of the
canonical identity comparison.
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

/-- The underlying forward arrow of an objectwise identity comparison is the identity. -/
@[simp, stacks 04Z4 "relative-inertia identity comparison forward underlying arrow"]
theorem app.hom.underlying
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : (relativeInertia S.hom).obj) :
    CategoryTheory.RelativeInertia.hom (app S A).hom = 𝟙 A.obj := sorry

/-- The underlying inverse arrow of an objectwise identity comparison is the identity. -/
@[simp, stacks 04Z4 "relative-inertia identity comparison inverse underlying arrow"]
theorem app.inv.underlying
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : (relativeInertia S.hom).obj) :
    CategoryTheory.RelativeInertia.hom (app S A).inv = 𝟙 A.obj := sorry

end mapIdIso

namespace mapIdIso

/-- The forward component of the pseudo-comma relative-inertia identity comparison is its
explicit objectwise comparison. -/
@[simp, stacks 04Z4 "relative-inertia identity comparison forward component"]
theorem hom.app
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : (relativeInertia S.hom).obj) :
    (pseudoComma.mapIdIso S).hom.toNatTrans.app A = (app S A).hom := sorry

/-- The inverse component of the pseudo-comma relative-inertia identity comparison is its
explicit inverse objectwise comparison. -/
@[simp, stacks 04Z4 "relative-inertia identity comparison inverse component"]
theorem inv.app
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : (relativeInertia S.hom).obj) :
    (pseudoComma.mapIdIso S).inv.toNatTrans.app A = (app S A).inv := sorry

/-- Every forward component of the packaged pseudo-comma identity comparison is vertical over
the identity base arrow. -/
@[stacks 04Z4 "relative-inertia packaged identity comparison forward verticality"]
theorem hom.app.isHomLift
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : (relativeInertia S.hom).obj) :
    (relativeInertia S.hom).p.IsHomLift
      (𝟙 ((relativeInertia S.hom).p.obj A))
      ((pseudoComma.mapIdIso S).hom.toNatTrans.app A) := sorry

/-- Every inverse component of the packaged pseudo-comma identity comparison is vertical over
the identity base arrow. -/
@[stacks 04Z4 "relative-inertia packaged identity comparison inverse verticality"]
theorem inv.app.isHomLift
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : (relativeInertia S.hom).obj) :
    (relativeInertia S.hom).p.IsHomLift
      (𝟙 ((relativeInertia S.hom).p.obj A))
      ((pseudoComma.mapIdIso S).inv.toNatTrans.app A) := sorry

end mapIdIso

end
end RelativeInertia.pseudoComma
end CategoryTheory.BasedCategory
