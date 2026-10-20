/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Based.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of identity sections for based inertia

This leaf owns the canonical based functors selecting identity automorphisms in
relative and absolute inertia. Computation lemmas belong to
`Section.Computations`.
-/

@[expose] public section

universe u v u₁ v₁ u₁' v₁'

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

section IdentitySection

variable {X : BasedCategory.{v₁, u₁} C} {Y : BasedCategory.{v₁', u₁'} C}

/-- The neutral relative-inertia section commutes with projection to the base. -/
@[stacks 04Z3 "relative-inertia section projection computation"]
theorem RelativeInertia.identitySection.comm (F : X ⥤ᵇ Y) :
    CategoryTheory.RelativeInertia.identitySection F.toFunctor ⋙
        (relativeInertia F).p =
      X.p := sorry
/- Proof strategy: unfold the relative-inertia projection and the neutral section; both
composites have the same object and morphism maps. -/

/-- The identity automorphisms define the canonical section of based relative inertia. -/
@[stacks 04Z3 "(1) relative-inertia neutral section"]
def RelativeInertia.identitySection (F : X ⥤ᵇ Y) :
    X ⥤ᵇ relativeInertia F where
  toFunctor := CategoryTheory.RelativeInertia.identitySection F.toFunctor
  w := RelativeInertia.identitySection.comm F

/-- The neutral absolute-inertia section commutes with projection to the base. -/
@[stacks 04Z3 "absolute-inertia section projection computation"]
theorem Inertia.identitySection.comm (X : BasedCategory.{v₁, u₁} C) :
    CategoryTheory.RelativeInertia.identitySection X.toBase.toFunctor ⋙
        (inertia X).p =
      X.p := sorry
/- Proof strategy: specialize `RelativeInertia.identitySection.comm` to `X.toBase`. -/

/-- The identity automorphisms define the canonical section of based absolute inertia. -/
@[stacks 04Z3 "(2) absolute-inertia neutral section"]
def Inertia.identitySection (X : BasedCategory.{v₁, u₁} C) :
    X ⥤ᵇ inertia X where
  toFunctor := CategoryTheory.RelativeInertia.identitySection X.toBase.toFunctor
  w := Inertia.identitySection.comm X

end IdentitySection

end BasedCategory
end CategoryTheory

/- Axiom audit: the public section owners store only the canonical neutral functor and a
Prop-valued commutation proof. -/
