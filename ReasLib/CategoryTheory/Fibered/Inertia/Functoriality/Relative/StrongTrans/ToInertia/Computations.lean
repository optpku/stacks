/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.StrongTrans.ToInertia.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.ToInertia.Computations

import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for the relative-to-absolute inertia strong transformation

This leaf exposes its canonical component and naturality owners together with objectwise
forward and inverse readouts.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

noncomputable section

namespace RelativeInertia
namespace pseudoComma

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}

namespace toInertia.strongTrans

/-- The component of the relative-to-absolute inertia transformation is the canonical based
comparison from relative inertia to absolute inertia of the left endpoint. -/
@[simp, stacks 04Z5 "relative-to-absolute strong transformation component"]
theorem app
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))) :
    (toInertia.strongTrans C).app S =
      RelativeInertia.toInertia S.hom := sorry

/-- The underlying functor of a relative-to-absolute component is the canonical relative
inertia map determined by the structural pseudo-comma arrow. -/
@[simp, stacks 04Z5 "relative-to-absolute strong transformation functor computation"]
theorem app.toFunctor
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))) :
    ((toInertia.strongTrans C).app S).toFunctor =
      (RelativeInertia.toInertia S.hom).toFunctor := sorry

/-- The component sends each relative-inertia object to the corresponding canonical
relative-to-absolute object. -/
@[simp, stacks 04Z5 "relative-to-absolute strong transformation object computation"]
theorem app.obj
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : ((pseudofunctor C).obj S).obj) :
    ((toInertia.strongTrans C).app S).toFunctor.obj A =
      (RelativeInertia.toInertia S.hom).toFunctor.obj A := sorry

/-- Passing to absolute inertia retains the underlying object. -/
@[simp, stacks 04Z5 "relative-to-absolute strong transformation underlying object"]
theorem app.obj.underlying
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : ((pseudofunctor C).obj S).obj) :
    (((toInertia.strongTrans C).app S).toFunctor.obj A).obj = A.obj := sorry

/-- Passing to absolute inertia retains the chosen automorphism. -/
@[simp, stacks 04Z5 "relative-to-absolute strong transformation automorphism"]
theorem app.obj.aut
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    (A : ((pseudofunctor C).obj S).obj) :
    (((toInertia.strongTrans C).app S).toFunctor.obj A).aut = A.aut := sorry

/-- Passing to absolute inertia retains the arrow underlying a relative-inertia morphism. -/
@[simp, stacks 04Z5 "relative-to-absolute strong transformation arrow"]
theorem app.hom.underlying
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C)))
    {A B : ((pseudofunctor C).obj S).obj} (phi : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom
        (((toInertia.strongTrans C).app S).toFunctor.map phi) =
      CategoryTheory.RelativeInertia.hom phi := sorry

/-- The naturality isomorphism of the relative-to-absolute transformation is the canonical
pseudo-comma square comparison. -/
@[simp, stacks 04Z5 "relative-to-absolute strong transformation naturality"]
theorem naturality (f : S ⟶ T) :
    (toInertia.strongTrans C).naturality f =
      toInertiaIso f := sorry

/-- The forward naturality component is the canonical objectwise relative-to-absolute
comparison. -/
@[simp, stacks 04Z5 "relative-to-absolute strong transformation forward component"]
theorem naturality.hom.app
    (f : S ⟶ T) (A : ((pseudofunctor C).obj S).obj) :
    ((toInertia.strongTrans C).naturality f).hom.toNatTrans.app A =
      (toInertiaIso f).hom.toNatTrans.app A := sorry

/-- The inverse naturality component is the reverse canonical objectwise
relative-to-absolute comparison. -/
@[simp, stacks 04Z5 "relative-to-absolute strong transformation inverse component"]
theorem naturality.inv.app
    (f : S ⟶ T) (A : ((pseudofunctor C).obj S).obj) :
    ((toInertia.strongTrans C).naturality f).inv.toNatTrans.app A =
      (toInertiaIso f).inv.toNatTrans.app A := sorry

/-- The arrow underlying each forward naturality component is the identity on the image under
the left endpoint. -/
@[simp, stacks 04Z5 "relative-to-absolute strong transformation forward underlying arrow"]
theorem naturality.hom.app.underlying
    (f : S ⟶ T) (A : ((pseudofunctor C).obj S).obj) :
    CategoryTheory.RelativeInertia.hom
        (((toInertia.strongTrans C).naturality f).hom.toNatTrans.app A) =
      𝟙 ((Bicategory.PseudoComma.left f).toFunctor.obj A.obj) := sorry

/-- The arrow underlying each inverse naturality component is the identity on the image under
the left endpoint. -/
@[simp, stacks 04Z5 "relative-to-absolute strong transformation inverse underlying arrow"]
theorem naturality.inv.app.underlying
    (f : S ⟶ T) (A : ((pseudofunctor C).obj S).obj) :
    CategoryTheory.RelativeInertia.hom
        (((toInertia.strongTrans C).naturality f).inv.toNatTrans.app A) =
      𝟙 ((Bicategory.PseudoComma.left f).toFunctor.obj A.obj) := sorry

end toInertia.strongTrans

end pseudoComma
end RelativeInertia

end

end BasedCategory
end CategoryTheory
