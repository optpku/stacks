/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Fibers
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.FiberObject.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism classes in discrete fibers

For a discrete fibration, every fiber is a discrete category. Consequently its set of
isomorphism classes is canonically identified with its type of objects. This file packages those
fiberwise identifications as an isomorphism of presheaves.
-/

@[expose] public section

universe w u v uS vS

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace Functor.IsDiscreteFibration

variable {S : Type uS} [Category.{vS} S]

/-- In a discrete fiber, taking the unique representative and taking the isomorphism class are
mutually inverse. This is the component of `fiberClassesIso`. -/
@[stacks 0045 "discrete-fibre class comparison component",
  stacks 02Y2 "discrete-fibre class comparison component",
  stacks 04SI "discrete-fibre class comparison component"]
def fiberClassesIso.app
    (p : S ⥤ C) [p.IsDiscreteFibration] (U : Cᵒᵖ) :
    (Functor.fiberIsoClassPresheaf p).obj U ≅ p.fiberObjectPresheaf.obj U where
  hom := TypeCat.ofHom (𝟭 (p.Fiber (unop U))).isoClassesToObj
  inv := TypeCat.ofHom fun x ↦ Quotient.mk'' x
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The component isomorphisms between fiber classes and fiber objects commute with restriction
in the base. -/
theorem fiberClassesIso.naturality
    (p : S ⥤ C) [p.IsDiscreteFibration] {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Functor.fiberIsoClassPresheaf p).map f ≫ (fiberClassesIso.app p V).hom =
      (fiberClassesIso.app p U).hom ≫ p.fiberObjectPresheaf.map f := sorry

/-- For a discrete fibration, the presheaf of fiberwise isomorphism classes is canonically
isomorphic to the presheaf of fiber objects. -/
@[stacks 0045 "discrete-fibre comparison",
  stacks 02Y2 "discrete-fibre comparison",
  stacks 04SI "discrete-fibre comparison"]
noncomputable def fiberClassesIso
    (p : S ⥤ C) [p.IsDiscreteFibration] :
    Functor.fiberIsoClassPresheaf p ≅ p.fiberObjectPresheaf :=
  NatIso.ofComponents (fiberClassesIso.app p) (fun f ↦ fiberClassesIso.naturality p f)

/-- The canonical comparison between fiber classes and fiber objects after both presheaves are
placed in a chosen ambient universe. -/
@[stacks 0045 "size-stable discrete-fibre comparison",
  stacks 02Y2 "size-stable discrete-fibre comparison",
  stacks 04SI "size-stable discrete-fibre comparison"]
noncomputable def fiberClassesIso.ulift
    (p : S ⥤ C) [p.IsDiscreteFibration] :
    (Functor.fiberIsoClassPresheaf p ⋙
        (CategoryTheory.uliftFunctor.{max w uS, uS} :
          Type uS ⥤ Type (max w uS))) ≅
      (p.fiberObjectPresheaf ⋙
        (CategoryTheory.uliftFunctor.{max w uS, uS} :
          Type uS ⥤ Type (max w uS))) :=
  Functor.isoWhiskerRight (fiberClassesIso p)
    (CategoryTheory.uliftFunctor.{max w uS, uS})

namespace fiberClassesIso.hom

/-- On a represented isomorphism class, the forward fiberwise map returns the representative
object. -/
@[simp]
theorem app_mk
    (p : S ⥤ C) [p.IsDiscreteFibration]
    (U : Cᵒᵖ) (x : p.Fiber (unop U)) :
    (fiberClassesIso p).hom.app U (Quotient.mk'' x) = x := sorry

end fiberClassesIso.hom

namespace fiberClassesIso.inv

/-- The inverse fiberwise map sends an object to its represented isomorphism class. -/
@[simp]
theorem app
    (p : S ⥤ C) [p.IsDiscreteFibration]
    (U : Cᵒᵖ) (x : p.Fiber (unop U)) :
    (fiberClassesIso p).inv.app U x = Quotient.mk'' x := sorry

end fiberClassesIso.inv

namespace fiberClassesIso.ulift

/-- On a lifted represented class, the lifted forward comparison returns the lifted
representative object. -/
@[simp]
theorem hom.app_mk
    (p : S ⥤ C) [p.IsDiscreteFibration]
    (U : Cᵒᵖ) (x : p.Fiber (unop U)) :
    (fiberClassesIso.ulift.{w} p).hom.app U
        (ULift.up (Quotient.mk'' x)) = ULift.up x := sorry

/-- The inverse lifted comparison sends a lifted fiber object to its lifted isomorphism class. -/
@[simp]
theorem inv.app
    (p : S ⥤ C) [p.IsDiscreteFibration]
    (U : Cᵒᵖ) (x : p.Fiber (unop U)) :
    (fiberClassesIso.ulift.{w} p).inv.app U (ULift.up x) =
      ULift.up (Quotient.mk'' x) := sorry

end fiberClassesIso.ulift

end Functor.IsDiscreteFibration

end CategoryTheory
