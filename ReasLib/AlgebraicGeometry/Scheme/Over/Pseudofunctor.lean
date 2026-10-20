/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Scheme slices as a pseudofunctor

Pullback along a morphism of schemes gives the contravariant pseudofunctor whose fibre over
`X` is the slice category `Over X`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped CategoryTheory.Bicategory

universe u

namespace AlgebraicGeometry.Scheme

/-- The associativity coherence for repeated pullback between scheme slices. -/
theorem overPseudofunctor_map₂_associator
    {X₀ X₁ X₂ X₃ : Scheme.{u}ᵒᵖ}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    (Cat.Hom.isoMk (Over.pullbackComp h.unop (f ≫ g).unop)).hom ≫
        (Cat.Hom.isoMk (Over.pullbackComp g.unop f.unop)).hom ▷
          (Over.pullback h.unop).toCatHom ≫
      (α_ (Over.pullback f.unop).toCatHom (Over.pullback g.unop).toCatHom
        (Over.pullback h.unop).toCatHom).hom ≫
      (Over.pullback f.unop).toCatHom ◁
        (Cat.Hom.isoMk (Over.pullbackComp h.unop g.unop)).inv ≫
      (Cat.Hom.isoMk (Over.pullbackComp (g ≫ h).unop f.unop)).inv =
        eqToHom rfl := sorry

/-- The left-unit coherence for pullback between scheme slices. -/
theorem overPseudofunctor_map₂_leftUnitor
    {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (Over.pullbackComp f.unop (𝟙 X).unop)).hom ≫
        (Cat.Hom.isoMk Over.pullbackId).hom ▷ (Over.pullback f.unop).toCatHom ≫
      (λ_ (Over.pullback f.unop).toCatHom).hom = eqToHom rfl := sorry

/-- The right-unit coherence for pullback between scheme slices. -/
theorem overPseudofunctor_map₂_rightUnitor
    {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (Over.pullbackComp (𝟙 Y).unop f.unop)).hom ≫
        (Over.pullback f.unop).toCatHom ◁ (Cat.Hom.isoMk Over.pullbackId).hom ≫
      (ρ_ (Over.pullback f.unop).toCatHom).hom = eqToHom rfl := sorry

/-- The contravariant pseudofunctor of scheme slices, with transition functors given by
pullback of schemes over schemes. -/
noncomputable def overPseudofunctor :
    LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (Over X.unop))
    (fun f ↦ (Over.pullback f.unop).toCatHom)
    (fun _ ↦ Cat.Hom.isoMk Over.pullbackId)
    (fun f g ↦ Cat.Hom.isoMk (Over.pullbackComp g.unop f.unop))
    overPseudofunctor_map₂_associator
    overPseudofunctor_map₂_leftUnitor
    overPseudofunctor_map₂_rightUnitor

/-- The fibre of `overPseudofunctor` at `X` is the category of schemes over `X`. -/
theorem overPseudofunctor_obj (X : Scheme.{u}) :
    overPseudofunctor.obj (.mk (.op X)) = Cat.of (Over X) := sorry

/-- The action of `overPseudofunctor` on a scheme morphism is pullback in the slice category. -/
theorem overPseudofunctor_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (overPseudofunctor.map f.op.toLoc).toFunctor = Over.pullback f := sorry

end AlgebraicGeometry.Scheme
