module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Lift.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of Pointwise Categorical Pullback Lifts

This leaf sends morphisms between compatible indexed cones to morphisms between their universal
lifts, with fibrewise, reindexing, identity, and composition computation rules.
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

/-- Compatibility of the component modifications of a morphism between indexed
categorical-pullback cones. -/
theorem Pullback.Lift.Hom.cone.w
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) (U : E) :
    Functor.whiskerRight (φ.fst.app U) (L.app (v.obj U)) ≫
        (Pullback.Lift.Fiber.cone L R Q.fst Q.snd Q.iso U).iso.hom =
      (Pullback.Lift.Fiber.cone L R P.fst P.snd P.iso U).iso.hom ≫
        Functor.whiskerRight (φ.snd.app U) (R.app (v.obj U)) := sorry

/-- A morphism between indexed categorical-pullback cones induces a morphism between their
ordinary commutative squares in every fiber. -/
noncomputable def Pullback.Lift.Hom.cone
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) (U : E) :
    Pullback.Lift.Fiber.cone L R P.fst P.snd P.iso U ⟶
      Pullback.Lift.Fiber.cone L R Q.fst Q.snd Q.iso U where
  fst := φ.fst.app U
  snd := φ.snd.app U
  w := Pullback.Lift.Hom.cone.w L R φ U

/-- The first natural-transformation component of a fiberwise cone morphism is inherited from
the first indexed modification. -/
@[simp]
theorem Pullback.Lift.Hom.cone.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) (U : E) :
    (Pullback.Lift.Hom.cone L R φ U).fst = φ.fst.app U := sorry

/-- The second natural-transformation component of a fiberwise cone morphism is inherited from
the second indexed modification. -/
@[simp]
theorem Pullback.Lift.Hom.cone.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) (U : E) :
    (Pullback.Lift.Hom.cone L R φ U).snd = φ.snd.app U := sorry

/-- The component natural transformation between pointwise-pullback lifts induced by a
morphism of indexed categorical-pullback cones. -/
noncomputable def Pullback.Lift.Hom.app
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) (U : E) :
    Pullback.Lift.Fiber.functor L R P.fst P.snd P.iso U ⟶
      Pullback.Lift.Fiber.functor L R Q.fst Q.snd Q.iso U :=
  (CatCommSqOver.toFunctorToCategoricalPullback
    (L.app (v.obj U)) (R.app (v.obj U)) _).map (Pullback.Lift.Hom.cone L R φ U)

/-- The first component of the natural transformation between pointwise-pullback lifts is the
first component of the cone morphism. -/
@[simp]
theorem Pullback.Lift.Hom.app.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    ((Pullback.Lift.Hom.app L R φ U).app x).fst =
      (φ.fst.app U).app x := sorry

/-- The second component of the natural transformation between pointwise-pullback lifts is the
second component of the cone morphism. -/
@[simp]
theorem Pullback.Lift.Hom.app.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    ((Pullback.Lift.Hom.app L R φ U).app x).snd =
      (φ.snd.app U).app x := sorry

/-- The component natural transformations induced by a morphism of indexed
categorical-pullback cones commute with base reindexing. -/
theorem Pullback.Lift.Hom.map.naturality
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) {U V : E} (f : V ⟶ U)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    ((Pullback.Lift.ofCone L R P.fst P.snd P.iso).naturality f).hom.app x ≫
        ((Pullback.pseudofunctor L R).map (v.map f).op.toLoc).toFunctor.map
          ((Pullback.Lift.Hom.app L R φ U).app x) =
      (Pullback.Lift.Hom.app L R φ V).app
          ((K.map f.op.toLoc).toFunctor.obj x) ≫
        ((Pullback.Lift.ofCone L R Q.fst Q.snd Q.iso).naturality f).hom.app x := sorry

/-- A morphism of compatible pairs of indexed functors induces a modification between their
pointwise-pullback lifts. -/
@[stacks 0040 "morphism action for pointwise categorical pseudo-pullback lifts"]
noncomputable def Pullback.Lift.Hom.map
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) :
    Pullback.Lift.ofCone L R P.fst P.snd P.iso ⟶
      Pullback.Lift.ofCone L R Q.fst Q.snd Q.iso where
  app U := Pullback.Lift.Hom.app L R φ U
  naturality f x := Pullback.Lift.Hom.map.naturality L R φ f x

/-- Components of the modification induced between pointwise-pullback lifts are the ordinary
natural transformations obtained from the fiberwise categorical-pullback universal property. -/
@[simp]
theorem Pullback.Lift.Hom.map.app
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) (U : E) :
    (Pullback.Lift.Hom.map L R φ).app U = Pullback.Lift.Hom.app L R φ U := sorry

/-- The lifted modification projects to the first component of the original cone morphism. -/
@[simp]
theorem Pullback.Lift.Hom.map.app.fst
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (((Pullback.Lift.Hom.map L R φ).app U).app x).fst =
      (φ.fst.app U).app x := sorry

/-- The lifted modification projects to the second component of the original cone morphism. -/
@[simp]
theorem Pullback.Lift.Hom.map.app.snd
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) (U : E)
    (x : K.obj (LocallyDiscrete.mk (op U))) :
    (((Pullback.Lift.Hom.map L R φ).app U).app x).snd =
      (φ.snd.app U).app x := sorry

/-- Pointwise-pullback lifting preserves identity cone morphisms. -/
theorem Pullback.Lift.Hom.map.id
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    (P :
      (postcomp v K L) ⊡ (postcomp v K R)) :
    Pullback.Lift.Hom.map L R (𝟙 P) =
      𝟙 (Pullback.Lift.ofCone L R P.fst P.snd P.iso) := sorry

/-- Pointwise-pullback lifting preserves composition of cone morphisms. -/
theorem Pullback.Lift.Hom.map.comp
    {K : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vK, uK}}
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {P Q S :
      (postcomp v K L) ⊡ (postcomp v K R)}
    (φ : P ⟶ Q) (ψ : Q ⟶ S) :
    Pullback.Lift.Hom.map L R (φ ≫ ψ) =
      Pullback.Lift.Hom.map L R φ ≫ Pullback.Lift.Hom.map L R ψ := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
