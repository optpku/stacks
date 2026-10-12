/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans.Lift.Construction
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

/-!
# Modifications between lifted strong transformations

An ambient modification lifts pointwise between the canonical bilateral lifts of its source and
target strong transformations. Its `2`-morphism components are unchanged after forgetting the
full-subbicategory wrapper.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

universe w v u wA vA uA

namespace ObjectProperty.FullSubbicategory.StrongTrans.Modification

variable {D : Type u} [Bicategory.{w, v} D]
variable {P : ObjectProperty D}
variable {A : Type uA} [Bicategory.{wA, vA} A]
variable (F G : Pseudofunctor A D)
variable (hF : ∀ X : A, P (F.obj X)) (hG : ∀ X : A, P (G.obj X))
variable {η θ : Pseudofunctor.StrongTrans F G}

/-- A component of an ambient modification, regarded as a `2`-morphism in the selected full
subbicategory. -/
private def app (Γ : Pseudofunctor.StrongTrans.Modification η θ) (X : A) :
    (StrongTrans.liftPseudofunctor F G hF hG η).app X ⟶
      (StrongTrans.liftPseudofunctor F G hF hG θ).app X :=
  Bicategory.InducedBicategory.mkHom₂ (Γ.app X)

/-- Naturality of the pointwise lifted modification. -/
private theorem naturality
    (Γ : Pseudofunctor.StrongTrans.Modification η θ) :
    ∀ {X Y : A} (f : X ⟶ Y),
      (FullSubbicategory.liftPseudofunctor F hF).map f ◁ app F G hF hG Γ Y ≫
          ((StrongTrans.liftPseudofunctor F G hF hG θ).naturality f).hom =
        ((StrongTrans.liftPseudofunctor F G hF hG η).naturality f).hom ≫
          app F G hF hG Γ X ▷
            (FullSubbicategory.liftPseudofunctor G hG).map f := sorry

/-- Lift an ambient modification between strong transformations to a modification between their
canonical bilateral full-subbicategory lifts. -/
def liftPseudofunctor
    (Γ : Pseudofunctor.StrongTrans.Modification η θ) :
    Pseudofunctor.StrongTrans.Modification
      (StrongTrans.liftPseudofunctor F G hF hG η)
      (StrongTrans.liftPseudofunctor F G hF hG θ) where
  app := app F G hF hG Γ
  naturality := naturality F G hF hG Γ

end ObjectProperty.FullSubbicategory.StrongTrans.Modification

end CategoryTheory
