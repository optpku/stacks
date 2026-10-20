/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open DividedPowers

universe u

/-- A divided power ring is a commutative ring equipped with an ideal carrying divided powers. -/
@[stacks 07GU "bundled divided-power rings"]
def DividedPowerRing :=
  Σ ring : CommRingCat.{u}, Σ ideal : Ideal ring, DividedPowers ideal

/-- The underlying carrier of a divided power ring. -/
def DividedPowerRing.carrier (ring : DividedPowerRing.{u}) : Type u :=
  ring.1

/-- The commutative ring structure on the carrier of a divided power ring. -/
instance DividedPowerRing.commRing (ring : DividedPowerRing.{u}) : CommRing ring.carrier :=
  ring.1.commRing

/-- A bundled divided power ring coerces to its underlying carrier type. -/
instance : CoeSort DividedPowerRing (Type u) := ⟨DividedPowerRing.carrier⟩

/-- The distinguished ideal of a divided power ring. -/
def DividedPowerRing.ideal (ring : DividedPowerRing.{u}) : Ideal ring :=
  ring.2.1

/-- The divided power structure on the distinguished ideal of a divided power ring. -/
def DividedPowerRing.dividedPowers (ring : DividedPowerRing.{u}) : DividedPowers ring.ideal :=
  ring.2.2

namespace DividedPowers.DPMorphism

/-- Composing a divided power morphism on the source side with the identity does not change it. -/
@[simp]
theorem id_comp {A B : Type*} [CommSemiring A] [CommSemiring B]
    {I : Ideal A} {J : Ideal B} {γ : DividedPowers I} {δ : DividedPowers J}
    (f : DPMorphism γ δ) :
    DPMorphism.comp f (DPMorphism.id γ) = f := sorry

/-- Composing a divided power morphism on the target side with the identity does not change it. -/
@[simp]
theorem comp_id {A B : Type*} [CommSemiring A] [CommSemiring B]
    {I : Ideal A} {J : Ideal B} {γ : DividedPowers I} {δ : DividedPowers J}
    (f : DPMorphism γ δ) :
    DPMorphism.comp (DPMorphism.id δ) f = f := sorry

/-- Composition of divided power morphisms is associative. -/
@[simp]
theorem comp_assoc {A B C D : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring C] [CommSemiring D]
    {I : Ideal A} {J : Ideal B} {K : Ideal C} {L : Ideal D}
    {γ : DividedPowers I} {δ : DividedPowers J}
    {ε : DividedPowers K} {ζ : DividedPowers L}
    (f : DPMorphism γ δ) (g : DPMorphism δ ε) (h : DPMorphism ε ζ) :
    DPMorphism.comp h (DPMorphism.comp g f) = DPMorphism.comp (DPMorphism.comp h g) f := sorry

end DividedPowers.DPMorphism

namespace DividedPowerRing

/-- The bundled divided power ring attached to a commutative ring equipped with divided powers on
an ideal. -/
abbrev of (A : Type u) [CommRing A] (I : Ideal A) (hI : DividedPowers I) : DividedPowerRing :=
  ⟨CommRingCat.of A, I, hI⟩

/-- Morphisms of divided power rings are the canonical bundled divided power morphisms. -/
instance instCategory : Category DividedPowerRing where
  Hom A B := DPMorphism A.dividedPowers B.dividedPowers
  id A := DPMorphism.id A.dividedPowers
  comp f g := DPMorphism.comp g f
  id_comp := DPMorphism.id_comp
  comp_id := DPMorphism.comp_id
  assoc := DPMorphism.comp_assoc

namespace Implementation

/-- Converting a divided power morphism to a categorical morphism and back is the identity. -/
theorem concreteHomOfHom {A B : DividedPowerRing}
    (f : DPMorphism A.dividedPowers B.dividedPowers) :
    (fun g : A ⟶ B ↦ (g : DPMorphism A.dividedPowers B.dividedPowers))
      ((fun g : DPMorphism A.dividedPowers B.dividedPowers ↦ (g : A ⟶ B)) f) = f := sorry

/-- Converting a categorical divided power morphism to a bundled morphism and back is the
identity. -/
theorem concreteOfHomHom {A B : DividedPowerRing} (f : A ⟶ B) :
    (fun g : DPMorphism A.dividedPowers B.dividedPowers ↦ (g : A ⟶ B))
      ((fun g : A ⟶ B ↦ (g : DPMorphism A.dividedPowers B.dividedPowers)) f) = f := sorry

/-- The categorical identity morphism acts as the identity function on the carrier. -/
theorem concreteIdApply {A : DividedPowerRing} (x : A) :
    DPMorphism.id A.dividedPowers x = x := sorry

/-- Categorical composition of divided power morphisms acts by function composition. -/
theorem concreteCompApply {A B C : DividedPowerRing} (f : A ⟶ B) (g : B ⟶ C)
    (x : A) : (DPMorphism.comp g f).toRingHom x = g.toRingHom (f.toRingHom x) := sorry

end Implementation

/-- The category of divided power rings is concrete over its carrier types. -/
instance instConcreteCategory : ConcreteCategory DividedPowerRing
    (fun A B ↦ DPMorphism A.dividedPowers B.dividedPowers) where
  hom := fun f ↦ f
  ofHom := fun f ↦ f
  hom_ofHom := Implementation.concreteHomOfHom
  ofHom_hom := Implementation.concreteOfHomHom
  id_apply := Implementation.concreteIdApply
  comp_apply := Implementation.concreteCompApply

/-- A divided power morphism as a morphism in the category `DividedPowerRing`. -/
abbrev ofHom {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}
    {hI : DividedPowers I} {hJ : DividedPowers J} (f : DPMorphism hI hJ) :
    of A I hI ⟶ of B J hJ :=
  f

namespace Implementation

/-- The underlying ring map of an identity divided power morphism is the identity. -/
theorem forgetCommRingMapId (A : DividedPowerRing) :
    CommRingCat.ofHom (DPMorphism.id A.dividedPowers).toRingHom =
      𝟙 (CommRingCat.of A) := sorry

/-- The underlying ring map preserves composition of divided power morphisms. -/
theorem forgetCommRingMapComp {A B C : DividedPowerRing} (f : A ⟶ B) (g : B ⟶ C) :
    CommRingCat.ofHom (DPMorphism.comp g f).toRingHom =
      CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom g.toRingHom := sorry

end Implementation

/-- The functor forgetting the distinguished ideal and divided powers of a divided power ring. -/
@[stacks 07GU "forgetful functor from divided-power rings"]
def forgetCommRing : DividedPowerRing ⥤ CommRingCat where
  obj A := CommRingCat.of A
  map f := CommRingCat.ofHom f.toRingHom
  map_id := Implementation.forgetCommRingMapId
  map_comp := Implementation.forgetCommRingMapComp

/-- The named forgetful functor agrees with the canonical forgetful functor on objects. -/
@[simp]
theorem forgetCommRing_obj (A : DividedPowerRing) :
    forgetCommRing.obj A = CommRingCat.of A := sorry

/-- The named forgetful functor sends a divided power morphism to its underlying ring map. -/
@[simp]
theorem forgetCommRing_map {A B : DividedPowerRing} (f : A ⟶ B) :
    forgetCommRing.map f = CommRingCat.ofHom f.toRingHom := sorry

namespace Implementation

/-- Forgetting a divided power ring to rings and then to types is the ordinary carrier functor. -/
theorem forgetCommRingCompForget :
    forgetCommRing ⋙ forget CommRingCat = forget DividedPowerRing := sorry

end Implementation

/-- The named functor `forgetCommRing` supplies the canonical forgetful functor to commutative
rings. -/
instance hasForgetToCommRingCat : HasForget₂ DividedPowerRing CommRingCat where
  forget₂ := forgetCommRing
  forget_comp := Implementation.forgetCommRingCompForget

/-- The canonical forgetful functor to commutative rings acts on objects as `forgetCommRing`. -/
@[simp]
theorem forget₂_commRingCat_obj (A : DividedPowerRing) :
    (forget₂ DividedPowerRing CommRingCat).obj A = CommRingCat.of A := sorry

/-- The canonical forgetful functor to commutative rings uses the underlying ring map. -/
@[simp]
theorem forget₂_commRingCat_map {A B : DividedPowerRing} (f : A ⟶ B) :
    (forget₂ DividedPowerRing CommRingCat).map f = CommRingCat.ofHom f.toRingHom := sorry

end DividedPowerRing
