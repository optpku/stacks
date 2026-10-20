module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Lift.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of the Universal Indexed Pullback Lift

This leaf assembles the fibrewise lift and its reindexing comparisons into the universal indexed
lift, together with its primary computation rules.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback Opposite
open scoped CategoricalPullback CategoryTheory.Bicategory

universe uC vC uD vD uE vE uF vF uG vG uH vH uK vK

namespace CategoryTheory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]
variable {u : C ⥤ D} {v : E ⥤ C}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable {H : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vH, uH}}

/-- The universal pointwise-pullback lift of two indexed functors equipped with an indexed
compatibility isomorphism. -/
@[stacks 0040 "lift into a pointwise categorical pseudo-pullback"]
noncomputable def Pullback.Lift.ofCone
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) :
    IndexedFunctor v K (Pullback.pseudofunctor L R) where
  app U := Pullback.Lift.Fiber.functor L R A B e U
  naturality f := Pullback.Lift.Naturality.iso L R A B e f
  naturality_id U x := Pullback.Lift.ofCone.naturality_id L R A B e U x
  naturality_comp f g x :=
    Pullback.Lift.ofCone.naturality_comp L R A B e f g x

/-- The component functor of a universal indexed lift is its fibrewise lift. -/
@[simp]
theorem Pullback.Lift.ofCone.app
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    (Pullback.Lift.ofCone L R A B e).app U =
      Pullback.Lift.Fiber.functor L R A B e U := sorry

/-- The reindexing comparison of a universal indexed lift is its explicit fibrewise comparison. -/
@[simp]
theorem Pullback.Lift.ofCone.naturality
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U V : E} (f : V ⟶ U) :
    (Pullback.Lift.ofCone L R A B e).naturality f =
      Pullback.Lift.Naturality.iso L R A B e f := sorry

/-- The first projection of a fibrewise universal lift is its left input functor. -/
@[simp]
theorem Pullback.Lift.ofCone.app.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    (Pullback.Lift.ofCone L R A B e).app U ⋙
        π₁ (L.app (v.obj U)) (R.app (v.obj U)) =
      A.app U := sorry

/-- The second projection of a fibrewise universal lift is its right input functor. -/
@[simp]
theorem Pullback.Lift.ofCone.app.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R) (U : E) :
    (Pullback.Lift.ofCone L R A B e).app U ⋙
        π₂ (L.app (v.obj U)) (R.app (v.obj U)) =
      B.app U := sorry

/-- Restricted-morphism transport through the first projection of the universal
pointwise-pullback lift is transport through the left input indexed functor. -/
@[simp]
theorem Pullback.Lift.ofCone.mapHom.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U₁ U₂ V : E} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : K.obj (LocallyDiscrete.mk (op U₁))}
    {y : K.obj (LocallyDiscrete.mk (op U₂))}
    (φ :
      (K.map f₁.op.toLoc).toFunctor.obj x ⟶
        (K.map f₂.op.toLoc).toFunctor.obj y) :
    ((Pullback.Lift.ofCone L R A B e).mapHom f₁ f₂ φ).fst =
      A.mapHom f₁ f₂ φ := sorry

/-- Restricted-morphism transport through the second projection of the universal
pointwise-pullback lift is transport through the right input indexed functor. -/
@[simp]
theorem Pullback.Lift.ofCone.mapHom.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (A : IndexedFunctor v K F) (B : IndexedFunctor v K G)
    (e : A.comp L ≅ B.comp R)
    {U₁ U₂ V : E} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : K.obj (LocallyDiscrete.mk (op U₁))}
    {y : K.obj (LocallyDiscrete.mk (op U₂))}
    (φ :
      (K.map f₁.op.toLoc).toFunctor.obj x ⟶
        (K.map f₂.op.toLoc).toFunctor.obj y) :
    ((Pullback.Lift.ofCone L R A B e).mapHom f₁ f₂ φ).snd =
      B.mapHom f₁ f₂ φ := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
