module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Basic

/-!
# Identity indexed functors
-/

@[expose] public section

universe uC vC uD vD uE vE uI vI uJ vJ uF vF uG vG uH vH uM vM uN vN

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace IndexedFunctor

variable {u : C ⥤ D}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vG, uG}}

/-- Naturality data for the identity indexed functor.  The ordinary functor unitors compare
restriction followed by an identity component with an identity component followed by
restriction. -/
noncomputable def idNaturality
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF})
    {U V : C} (f : V ⟶ U) :
    (F.map f.op.toLoc).toFunctor ⋙ 𝟭 _ ≅
      𝟭 _ ⋙ (F.map ((𝟭 C).map f).op.toLoc).toFunctor :=
  Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

/-- Identity coherence for the identity indexed functor. -/
theorem id_naturality_id
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF})
    (U : C) (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (𝟭 (F.obj (LocallyDiscrete.mk (Opposite.op U)))).map
          ((F.mapIdOp U).inv.toNatTrans.app x) ≫
        (idNaturality F (𝟙 U)).hom.app x =
      (F.mapIdOp' ((𝟭 C).obj U) ((𝟭 C).map (𝟙 U))
        ((𝟭 C).map_id U)).inv.toNatTrans.app
          ((𝟭 (F.obj (LocallyDiscrete.mk (Opposite.op U)))).obj x) := sorry

/-- Composition coherence for the identity indexed functor. -/
theorem id_naturality_comp
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF})
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (idNaturality F (g ≫ f)).hom.app x ≫
        (F.mapCompOp' ((𝟭 C).map f) ((𝟭 C).map g)
          ((𝟭 C).map (g ≫ f))
          ((𝟭 C).map_comp g f).symm).hom.toNatTrans.app
            ((𝟭 (F.obj (LocallyDiscrete.mk (Opposite.op U)))).obj x) =
      (𝟭 (F.obj (LocallyDiscrete.mk (Opposite.op W)))).map
          ((F.mapCompOp f g).hom.toNatTrans.app x) ≫
        (idNaturality F g).hom.app
          ((F.map f.op.toLoc).toFunctor.obj x) ≫
        (F.map ((𝟭 C).map g).op.toLoc).toFunctor.map
          ((idNaturality F f).hom.app x) := sorry

/-- The identity indexed functor on a contravariant `Cat`-valued pseudofunctor. -/
noncomputable def id
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}) :
    IndexedFunctor (𝟭 C) F F where
  app _ := 𝟭 _
  naturality f := idNaturality F f
  naturality_id U x := id_naturality_id F U x
  naturality_comp f g x := id_naturality_comp F f g x

/-- Components of the identity indexed functor are identity functors. -/
@[simp]
theorem id_app
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}) (U : C) :
    (id F).app U = 𝟭 _ := sorry

/-- Naturality of the identity indexed functor is the canonical comparison built from ordinary
functor unitors. -/
@[simp]
theorem id_naturality
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF})
    {U V : C} (f : V ⟶ U) :
    (id F).naturality f = idNaturality F f := sorry

/-- Restricted-morphism transport through the identity indexed functor is the original
morphism. -/
@[simp]
theorem id_mapHom
    (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF})
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : F.obj (LocallyDiscrete.mk (Opposite.op U₁))}
    {y : F.obj (LocallyDiscrete.mk (Opposite.op U₂))}
    (φ :
      (F.map f₁.op.toLoc).toFunctor.obj x ⟶
        (F.map f₂.op.toLoc).toFunctor.obj y) :
    (id F).mapHom f₁ f₂ φ = φ := sorry


end IndexedFunctor

end Pseudofunctor.LocallyDiscreteOpToCat

end CategoryTheory
