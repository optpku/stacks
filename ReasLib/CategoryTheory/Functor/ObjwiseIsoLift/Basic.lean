/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Equivalence

/-!
# Functors from prescribed objectwise preimages

Given a fully faithful functor `F : A ⥤ B`, an object assignment `jObj : B → A`, and
isomorphisms `X ≅ F.obj (jObj X)`, this file constructs the functorial lift with those prescribed
objects and the two comparison isomorphisms used by its universal and equivalence APIs.

This complements mathlib's `Functor.inv`: that construction chooses preimage objects from an
abstract equivalence instance, whereas `objwiseIsoLift` retains externally specified objects and
isomorphisms as concrete data.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

variable (F : A ⥤ B)

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The identity law for the lift determined by prescribed objectwise preimages. -/
private theorem objwiseIsoLift_map_id
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) (X : B) :
    F.preimage ((i X).inv ≫ 𝟙 X ≫ (i X).hom) = 𝟙 (jObj X) := sorry
/- Proof strategy: apply injectivity of `F.map`, rewrite `F.map_preimage`, and simplify the
identity and inverse-isomorphism factors. -/

/-- The composition law for the lift determined by prescribed objectwise preimages. -/
private theorem objwiseIsoLift_map_comp
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X))
    {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.preimage ((i X).inv ≫ (f ≫ g) ≫ (i Z).hom) =
      F.preimage ((i X).inv ≫ f ≫ (i Y).hom) ≫
        F.preimage ((i Y).inv ≫ g ≫ (i Z).hom) := sorry
/- Proof strategy: apply injectivity of `F.map`, rewrite each `F.map_preimage`, reassociate, and
cancel `(i Y).hom ≫ (i Y).inv`. -/

/-- The functor determined by prescribed objectwise preimages and their isomorphisms under a
fully faithful functor. -/
@[stacks 05SG "functor extending a chosen object assignment"]
noncomputable def objwiseIsoLift
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) : B ⥤ A where
  obj := jObj
  map {X Y} f := F.preimage ((i X).inv ≫ f ≫ (i Y).hom)
  map_id X := objwiseIsoLift_map_id F jObj i X
  map_comp f g := objwiseIsoLift_map_comp F jObj i f g

namespace objwiseIsoLift

/-- The prescribed lift has the specified object function. -/
@[simp]
theorem obj
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) (X : B) :
    (objwiseIsoLift F jObj i).obj X = jObj X := sorry
/- Proof strategy: unfold `objwiseIsoLift`. -/

/-- The prescribed lift maps a morphism by taking the fully faithful preimage of its conjugate. -/
@[simp]
theorem map
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X))
    {X Y : B} (f : X ⟶ Y) :
    (objwiseIsoLift F jObj i).map f =
      F.preimage ((i X).inv ≫ f ≫ (i Y).hom) := sorry
/- Proof strategy: unfold `objwiseIsoLift`. -/

/-- The prescribed objectwise isomorphisms are natural for `objwiseIsoLift`. -/
private theorem objwiseIsoLift_naturality
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X))
    {X Y : B} (f : X ⟶ Y) :
    f ≫ (i Y).hom =
      (i X).hom ≫ F.map ((objwiseIsoLift F jObj i).map f) := sorry
/- Proof strategy: apply injectivity of `F.map`, unfold `objwiseIsoLift`, rewrite
`F.map_preimage`, and cancel the components of `i` using the inverse laws. -/

/-- The prescribed objectwise isomorphisms, assembled into
`𝟭 B ≅ objwiseIsoLift F jObj i ⋙ F`. -/
noncomputable def compIso
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    𝟭 B ≅ objwiseIsoLift F jObj i ⋙ F :=
  NatIso.ofComponents i (fun f ↦ objwiseIsoLift_naturality F jObj i f)

namespace compIso

/-- The forward component of the named comparison for the prescribed lift is the supplied
objectwise isomorphism. -/
@[simp]
theorem hom.app
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) (X : B) :
    (compIso F jObj i).hom.app X = (i X).hom := sorry
/- Proof strategy: unfold `objwiseIsoLift.compIso` and use the component computation rule for
`NatIso.ofComponents`. -/

/-- The inverse component of the named comparison for the prescribed lift is the inverse of the
supplied objectwise isomorphism. -/
@[simp]
theorem inv.app
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) (X : B) :
    (compIso F jObj i).inv.app X = (i X).inv := sorry
/- Proof strategy: unfold `objwiseIsoLift.compIso` and use the inverse component computation rule
for `NatIso.ofComponents`. -/

end compIso

/-- Prescribed objectwise preimages exhibit `F` as essentially surjective. -/
theorem essSurj
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    F.EssSurj := sorry
/- Proof strategy: for each `X : B`, choose `jObj X`; the supplied isomorphism is the witness
required by `F.EssSurj`. -/

/-- The unit isomorphism making `objwiseIsoLift F jObj i` a quasi-inverse of `F`. -/
noncomputable def unitIso
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    𝟭 A ≅ F ⋙ objwiseIsoLift F jObj i :=
  fullyFaithfulCancelRight F <|
    F.leftUnitor ≪≫ F.rightUnitor.symm ≪≫
      isoWhiskerLeft F (compIso F jObj i) ≪≫
        (associator F (objwiseIsoLift F jObj i) F).symm

namespace unitIso

/-- The forward component of the prescribed unit is the fully faithful preimage of the
supplied isomorphism at `F.obj X`. -/
@[simp]
theorem hom.app
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) (X : A) :
    (unitIso F jObj i).hom.app X =
      F.preimage ((i (F.obj X)).hom) := sorry

/-- The inverse component of the prescribed unit is the fully faithful preimage of the inverse
supplied isomorphism at `F.obj X`. -/
@[simp]
theorem inv.app
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) (X : A) :
    (unitIso F jObj i).inv.app X =
      F.preimage ((i (F.obj X)).inv) := sorry

/-- Whiskering the prescribed unit on the right by `F` recovers the comparison isomorphism
from which fully faithful cancellation constructs it. -/
theorem whiskerRight
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    isoWhiskerRight (unitIso F jObj i) F =
      F.leftUnitor ≪≫ F.rightUnitor.symm ≪≫
        isoWhiskerLeft F (compIso F jObj i) ≪≫
          (associator F (objwiseIsoLift F jObj i) F).symm := sorry

end unitIso

end objwiseIsoLift

end CategoryTheory.Functor
