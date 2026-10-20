/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Choice
public import ReasLib.CategoryTheory.Functor.ObjwiseIsoLift.Basic

/-!
# Equivalence from a prescribed objectwise lift

The explicit `Functor.QuasiInverse` is the root owner. The mathlib equivalence and the
proposition-level `Functor.IsEquivalence` interface are derived from it.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.objwiseIsoLift

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable (F : A ⥤ B)

/-- The prescribed objectwise lift, its named unit, and its named counit packaged as explicit
quasi-inverse data for `F`. -/
@[stacks 05SG "chosen objectwise lift quasi-inverse"]
noncomputable def quasiInverse
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    Functor.QuasiInverse F where
  inverse := objwiseIsoLift F jObj i
  unitIso := unitIso F jObj i
  counitIso := (compIso F jObj i).symm

namespace quasiInverse

/-- The inverse functor of the prescribed quasi-inverse is the objectwise lift. -/
@[simp]
theorem inverse
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    (quasiInverse F jObj i).inverse = objwiseIsoLift F jObj i := sorry

/-- The unit of the prescribed quasi-inverse is the named fully faithful cancellation unit. -/
@[simp]
theorem unitIso
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    (quasiInverse F jObj i).unitIso = objwiseIsoLift.unitIso F jObj i := sorry

/-- The counit of the prescribed quasi-inverse is the inverse objectwise comparison. -/
@[simp]
theorem counitIso
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    (quasiInverse F jObj i).counitIso = (compIso F jObj i).symm := sorry

end quasiInverse

/-- Lemma 4.2.18 (2) (Stacks 05SG): the prescribed lift and `F` form an explicit equivalence of
categories, obtained by adjointifying the named quasi-inverse data. -/
@[stacks 05SG "chosen lift and original functor are quasi-inverse"]
noncomputable def equivalence
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) : A ≌ B :=
  (quasiInverse F jObj i).adjointifyUnit

namespace equivalence

/-- The forward functor of the prescribed equivalence is the original functor. -/
@[simp]
theorem functor
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    (equivalence F jObj i).functor = F := sorry

/-- The inverse functor of the prescribed equivalence is the prescribed lift. -/
@[simp]
theorem inverse
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    (equivalence F jObj i).inverse = objwiseIsoLift F jObj i := sorry

/-- The unit of the prescribed equivalence is the named unit obtained by fully faithful
cancellation. -/
@[simp]
theorem unitIso
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    (equivalence F jObj i).unitIso = objwiseIsoLift.unitIso F jObj i := sorry

/-- The forward unit component is the fully faithful preimage of the supplied isomorphism at
`F.obj X`. -/
@[simp]
theorem unitIso.hom.app
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) (X : A) :
    (equivalence F jObj i).unitIso.hom.app X =
      F.preimage ((i (F.obj X)).hom) := sorry

/-- The inverse unit component is the fully faithful preimage of the inverse supplied
isomorphism at `F.obj X`. -/
@[simp]
theorem unitIso.inv.app
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) (X : A) :
    (equivalence F jObj i).unitIso.inv.app X =
      F.preimage ((i (F.obj X)).inv) := sorry

/-- The counit of the prescribed equivalence is the inverse named comparison isomorphism. -/
@[simp]
theorem counitIso
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    (equivalence F jObj i).counitIso = (compIso F jObj i).symm := sorry

/-- The forward counit component is the inverse supplied objectwise isomorphism. -/
@[simp]
theorem counitIso.hom.app
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) (X : B) :
    (equivalence F jObj i).counitIso.hom.app X = (i X).inv := sorry

/-- The inverse counit component is the supplied objectwise isomorphism. -/
@[simp]
theorem counitIso.inv.app
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) (X : B) :
    (equivalence F jObj i).counitIso.inv.app X = (i X).hom := sorry

end equivalence

/-- Prescribed objectwise preimages under a fully faithful functor give the canonical
`Functor.IsEquivalence` proposition. -/
theorem isEquivalence
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    F.IsEquivalence := sorry

/- Axiom audit: the quasi-inverse owns explicit non-Prop functor and comparison data; the
equivalence is its standard adjointification. -/

end CategoryTheory.Functor.objwiseIsoLift
