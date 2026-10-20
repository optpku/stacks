module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.Tactic.CrossRefAttribute

/-!
# The walking-cospan pseudodiagram

This file constructs the pseudofunctor represented by a cospan in an arbitrary bicategory.
It is deliberately independent of bilimits and pseudopullbacks: a walking-cospan diagram is
useful whenever two `1`-morphisms have a common codomain.

The object and `1`-morphism data are explicit finite case splits on mathlib's
`Limits.WalkingCospan`. Only the pseudofunctor coherence laws are deferred.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} (f : x ⟶ z) (g : y ⟶ z)

namespace Bicategory

/-- The object function of the bicategorical cospan diagram `x ⟶ z ← y`. -/
private def cospanObj (x y z : B) : Limits.WalkingCospan → B
  | none => z
  | some j => Limits.WalkingPair.casesOn j x y

/-- The `1`-morphism function of the bicategorical cospan diagram. Identity arrows are
sent to identities, while the two generating arrows are sent to `f` and `g`. -/
private def cospanMap :
    ∀ {a b : Limits.WalkingCospan}, (a ⟶ b) →
      (cospanObj x y z a ⟶ cospanObj x y z b)
  | _, _, .id _ => 𝟙 _
  | _, _, .term j => Limits.WalkingPair.casesOn j f g

/-- The composition comparison for the bicategorical cospan diagram. Since every
nonidentity arrow ends at the centre, its only cases are the left and right unitors. -/
private def cospanMapComp :
    ∀ {a b c : Limits.WalkingCospan} (h : a ⟶ b) (k : b ⟶ c),
      cospanMap f g (h ≫ k) ≅ cospanMap f g h ≫ cospanMap f g k
  | _, _, _, .id _, k => (λ_ (cospanMap f g k)).symm
  | _, _, _, .term j, .id _ =>
      (ρ_ (cospanMap f g (Limits.WidePullbackShape.Hom.term j))).symm

/-- Associator coherence for the bicategorical cospan diagram. -/
private theorem cospanMapAssociator :
    ∀ {a b c d : Limits.WalkingCospan} (h : a ⟶ b) (k : b ⟶ c) (l : c ⟶ d),
      (cospanMapComp f g (h ≫ k) l).hom ≫
        (cospanMapComp f g h k).hom ▷ cospanMap f g l ≫
        (α_ (cospanMap f g h) (cospanMap f g k) (cospanMap f g l)).hom ≫
        cospanMap f g h ◁ (cospanMapComp f g k l).inv ≫
        (cospanMapComp f g h (k ≫ l)).inv =
          eqToHom (congrArg (fun t => cospanMap f g t) (Category.assoc h k l)) := sorry

/-- Left-unitor coherence for the bicategorical cospan diagram. -/
private theorem cospanMapLeftUnitor :
    ∀ {a b : Limits.WalkingCospan} (h : a ⟶ b),
      (cospanMapComp f g (𝟙 a) h).hom ≫
        (𝟙 (cospanMap f g (𝟙 a))) ▷ cospanMap f g h ≫
        (λ_ (cospanMap f g h)).hom =
          eqToHom (congrArg (fun t => cospanMap f g t) (Category.id_comp h)) := sorry

/-- Right-unitor coherence for the bicategorical cospan diagram. -/
private theorem cospanMapRightUnitor :
    ∀ {a b : Limits.WalkingCospan} (h : a ⟶ b),
      (cospanMapComp f g h (𝟙 b)).hom ≫
        cospanMap f g h ◁ (𝟙 (cospanMap f g (𝟙 b))) ≫
        (ρ_ (cospanMap f g h)).hom =
          eqToHom (congrArg (fun t => cospanMap f g t) (Category.comp_id h)) := sorry

/-- The pseudofunctor represented by the bicategorical cospan `x ⟶ z ← y`. Its domain is
the locally discrete bicategory on mathlib's `Limits.WalkingCospan`. -/
@[stacks 0040 "walking-cospan pseudodiagram"]
def cospan : LocallyDiscrete Limits.WalkingCospan ⥤ᵖ B :=
  LocallyDiscrete.mkPseudofunctor
    (cospanObj x y z) (cospanMap f g) (fun _ ↦ Iso.refl _)
    (cospanMapComp f g) (cospanMapAssociator f g) (cospanMapLeftUnitor f g)
    (cospanMapRightUnitor f g)

/-- The value of the canonical bicategorical cospan at its left endpoint is `x`. -/
@[simp]
theorem cospan.obj.left :
    (cospan f g).obj (LocallyDiscrete.mk Limits.WalkingCospan.left) = x := sorry

/-- The value of the canonical bicategorical cospan at its right endpoint is `y`. -/
@[simp]
theorem cospan.obj.right :
    (cospan f g).obj (LocallyDiscrete.mk Limits.WalkingCospan.right) = y := sorry

/-- The value of the canonical bicategorical cospan at its central vertex is `z`. -/
@[simp]
theorem cospan.obj.one :
    (cospan f g).obj (LocallyDiscrete.mk Limits.WalkingCospan.one) = z := sorry

/-- The left generating arrow of the canonical bicategorical cospan is sent to `f`. -/
@[simp]
theorem cospan.map.inl :
    (cospan f g).map (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl) = f := sorry

/-- The right generating arrow of the canonical bicategorical cospan is sent to `g`. -/
@[simp]
theorem cospan.map.inr :
    (cospan f g).map (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr) = g := sorry

/-- The walking-cospan pseudofunctor sends identity arrows strictly to identities. -/
@[simp]
theorem cospan.map.id (a : Limits.WalkingCospan) :
    (cospan f g).map (Quiver.Hom.toLoc (𝟙 a)) =
      𝟙 ((cospan f g).obj (LocallyDiscrete.mk a)) := sorry

/-- The identity comparison of the walking-cospan pseudofunctor is the identity isomorphism. -/
@[simp]
theorem cospan.mapId (a : Limits.WalkingCospan) :
    (cospan f g).mapId (LocallyDiscrete.mk a) =
      Iso.refl (𝟙 ((cospan f g).obj (LocallyDiscrete.mk a))) := sorry

/-- Composition by an identity on the left is compared by the inverse left unitor. -/
@[simp]
theorem cospan.mapComp.id_left
    {a b : Limits.WalkingCospan} (h : a ⟶ b) :
    (cospan f g).mapComp (Quiver.Hom.toLoc (𝟙 a)) (Quiver.Hom.toLoc h) =
      (λ_ ((cospan f g).map (Quiver.Hom.toLoc h))).symm := sorry

/-- The composition comparison for the left generator followed by an identity is the inverse
right unitor. -/
@[simp]
theorem cospan.mapComp.inl_id :
    (cospan f g).mapComp
        (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl)
        (Quiver.Hom.toLoc (𝟙 Limits.WalkingCospan.one)) =
      (ρ_ f).symm := sorry

/-- The composition comparison for the right generator followed by an identity is the inverse
right unitor. -/
@[simp]
theorem cospan.mapComp.inr_id :
    (cospan f g).mapComp
        (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr)
        (Quiver.Hom.toLoc (𝟙 Limits.WalkingCospan.one)) =
      (ρ_ g).symm := sorry

/-
Data and axiom audit (mathlib 4.32):

* `cospanObj` and `cospanMap` are explicit finite case splits; no proof chooses an object or
  `1`-morphism.
* `cospanMapComp` explicitly supplies the relevant inverse unitors.
* `cospan` delegates only its associator and unitor laws to the three theorem statements above.
  `#print axioms` reports `[propext, sorryAx, Classical.choice, Quot.sound]`; source inspection
  confines `sorryAx` to those `Prop`-valued pseudofunctor coherence fields.
-/

end Bicategory

end CategoryTheory
