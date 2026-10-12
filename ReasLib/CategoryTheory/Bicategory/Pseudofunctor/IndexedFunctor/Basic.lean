/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.HomCongr
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.OppositeLocallyDiscrete

/-!
# Basic indexed functors over a base functor

The universe-polymorphic owner for maps between contravariant `Cat`-valued
pseudofunctors over an ordinary base functor, together with restricted-hom
transport and its basic computation rules. Composition, coherence, and
fiberwise properties live in focused sibling modules.
-/

@[expose] public section

universe uC vC uD vD uE vE uI vI uJ vJ uF vF uG vG uH vH uM vM uN vN

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- A universe-polymorphic functor between contravariant `Cat`-valued pseudofunctors, lying over
a functor between their base categories.

The component at `U` maps the `F`-fiber over `U` to the `G`-fiber over `u.obj U`; `naturality`
compares restriction before and after applying that component. -/
structure IndexedFunctor
    (u : C ⥤ D)
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat)
    (G : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat) where
  /-- The functor between the two indexed fibers at a base object. -/
  app (U : C) :
    F.obj (LocallyDiscrete.mk (Opposite.op U)) ⥤
      G.obj (LocallyDiscrete.mk (Opposite.op (u.obj U)))
  /-- Restricting in `F` and then applying a component agrees, up to natural isomorphism, with
  applying the component and restricting in `G` along the mapped base arrow. -/
  naturality {U V : C} (f : V ⟶ U) :
    (F.map f.op.toLoc).toFunctor ⋙ app V ≅
      app U ⋙ (G.map (u.map f).op.toLoc).toFunctor
  /-- The naturality comparison over an identity is compatible with the identity constraints of
  `F` and `G`, including the displayed equality `u.map (𝟙 U) = 𝟙 (u.obj U)`. -/
  naturality_id (U : C)
      (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (app U).map ((F.mapIdOp U).inv.toNatTrans.app x) ≫
        (naturality (𝟙 U)).hom.app x =
      (G.mapIdOp' (u.obj U) (u.map (𝟙 U)) (u.map_id U)).inv.toNatTrans.app
        ((app U).obj x)
  /-- The naturality comparison over a composite is compatible with the two pseudofunctor
  composition constraints and the equality supplied by `u.map_comp`. -/
  naturality_comp {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
      (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (naturality (g ≫ f)).hom.app x ≫
        (G.mapCompOp' (u.map f) (u.map g) (u.map (g ≫ f))
          (u.map_comp g f).symm).hom.toNatTrans.app ((app U).obj x) =
      (app W).map ((F.mapCompOp f g).hom.toNatTrans.app x) ≫
        (naturality g).hom.app
          ((F.map f.op.toLoc).toFunctor.obj x) ≫
        (G.map (u.map g).op.toLoc).toFunctor.map
          ((naturality f).hom.app x)

namespace IndexedFunctor

variable {u : C ⥤ D}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vG, uG}}

/-- Transport a morphism between two restricted `F`-objects to the corresponding morphism
between restricted `G`-objects.  The two naturality components perform the endpoint
strictifications, while `H.app V` maps the middle arrow. -/
def mapHom (H : IndexedFunctor u F G)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (φ :
      (F.map f₁.op.toLoc).toFunctor.obj x ⟶
        (F.map f₂.op.toLoc).toFunctor.obj y) :
    (G.map (u.map f₁).op.toLoc).toFunctor.obj ((H.app U₁).obj x) ⟶
      (G.map (u.map f₂).op.toLoc).toFunctor.obj ((H.app U₂).obj y) :=
  (H.naturality f₁).inv.app x ≫
    (H.app V).map φ ≫
    (H.naturality f₂).hom.app y

/-- Computation formula for `IndexedFunctor.mapHom`. -/
theorem mapHom_eq (H : IndexedFunctor u F G)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (φ :
      (F.map f₁.op.toLoc).toFunctor.obj x ⟶
        (F.map f₂.op.toLoc).toFunctor.obj y) :
    H.mapHom f₁ f₂ φ =
      (H.naturality f₁).inv.app x ≫
        (H.app V).map φ ≫
        (H.naturality f₂).hom.app y := sorry

/-- Transporting an identity morphism between equal restrictions gives the identity. -/
@[simp]
theorem mapHom_id (H : IndexedFunctor u F G)
    {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    H.mapHom f f
        (𝟙 ((F.map f.op.toLoc).toFunctor.obj x)) =
      𝟙 ((G.map (u.map f).op.toLoc).toFunctor.obj ((H.app U).obj x)) := sorry

/-- Transport of restricted morphisms preserves composition. -/
theorem mapHom_comp (H : IndexedFunctor u F G)
    {U₁ U₂ U₃ V : C}
    (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂) (f₃ : V ⟶ U₃)
    {x₁ : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {x₂ : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    {x₃ : F.obj (LocallyDiscrete.mk (Opposite.op U₃))}
    (φ :
      (F.map f₁.op.toLoc).toFunctor.obj x₁ ⟶
        (F.map f₂.op.toLoc).toFunctor.obj x₂)
    (ψ :
      (F.map f₂.op.toLoc).toFunctor.obj x₂ ⟶
        (F.map f₃.op.toLoc).toFunctor.obj x₃) :
    H.mapHom f₁ f₃ (φ ≫ ψ) =
      H.mapHom f₁ f₂ φ ≫ H.mapHom f₂ f₃ ψ := sorry

/-- Inverse form of the identity coherence for an indexed functor.  This orientation is useful
when simplifying a morphism whose source has already been restricted in the target indexed
category. -/
theorem naturality_id_inv (H : IndexedFunctor u F G)
    (U : C) (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (H.naturality (𝟙 U)).inv.app x ≫
        (H.app U).map ((F.mapIdOp U).hom.toNatTrans.app x) =
      (G.mapIdOp' (u.obj U) (u.map (𝟙 U)) (u.map_id U)).hom.toNatTrans.app
        ((H.app U).obj x) := sorry

/-- Inverse form of the composition coherence for an indexed functor.  It rewrites transport
along two successive restrictions into transport along their composite. -/
theorem naturality_comp_inv (H : IndexedFunctor u F G)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (G.map (u.map g).op.toLoc).toFunctor.map
          ((H.naturality f).inv.app x) ≫
        (H.naturality g).inv.app
          ((F.map f.op.toLoc).toFunctor.obj x) ≫
        (H.app W).map ((F.mapCompOp f g).inv.toNatTrans.app x) =
      (G.mapCompOp' (u.map f) (u.map g) (u.map (g ≫ f))
          (u.map_comp g f).symm).inv.toNatTrans.app ((H.app U).obj x) ≫
        (H.naturality (g ≫ f)).inv.app x := sorry


end IndexedFunctor

end Pseudofunctor.LocallyDiscreteOpToCat

end CategoryTheory
