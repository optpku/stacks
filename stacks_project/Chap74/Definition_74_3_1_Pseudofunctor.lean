module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections

/-!
# Module-sheaf pseudofunctor on algebraic spaces

Pullback of sheaves of modules along morphisms of algebraic spaces over a scheme `S` is the
transition action of a Cat-valued pseudofunctor on `AlgebraicSpace S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open scoped CategoryTheory.Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Associativity coherence for successive module pullbacks of algebraic spaces. -/
theorem descentPseudofunctor_map₂_associator
    {S : Scheme.{u}} {X₀ X₁ X₂ X₃ : (AlgebraicSpace S)ᵒᵖ}
    (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) :
    (Cat.Hom.isoMk (pullbackComp h.unop (f ≫ g).unop).symm).hom ≫
        (Cat.Hom.isoMk (pullbackComp g.unop f.unop).symm).hom ▷
          (pullback h.unop).toCatHom ≫
      (α_ (pullback f.unop).toCatHom (pullback g.unop).toCatHom
        (pullback h.unop).toCatHom).hom ≫
      (pullback f.unop).toCatHom ◁
        (Cat.Hom.isoMk (pullbackComp h.unop g.unop).symm).inv ≫
      (Cat.Hom.isoMk (pullbackComp (g ≫ h).unop f.unop).symm).inv =
        eqToHom rfl := sorry

/-- Left-unit coherence for module pullback along an identity of algebraic spaces. -/
theorem descentPseudofunctor_map₂_leftUnitor
    {S : Scheme.{u}} {X Y : (AlgebraicSpace S)ᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (pullbackComp f.unop (𝟙 X).unop).symm).hom ≫
        (Cat.Hom.isoMk (SmallEtaleModuleGlueing.modulesPullbackId X.unop)).hom ▷
          (pullback f.unop).toCatHom ≫
      (λ_ (pullback f.unop).toCatHom).hom = eqToHom rfl := sorry

/-- Right-unit coherence for module pullback along an identity of algebraic spaces. -/
theorem descentPseudofunctor_map₂_rightUnitor
    {S : Scheme.{u}} {X Y : (AlgebraicSpace S)ᵒᵖ} (f : X ⟶ Y) :
    (Cat.Hom.isoMk (pullbackComp (𝟙 Y).unop f.unop).symm).hom ≫
        (pullback f.unop).toCatHom ◁
          (Cat.Hom.isoMk (SmallEtaleModuleGlueing.modulesPullbackId Y.unop)).hom ≫
      (ρ_ (pullback f.unop).toCatHom).hom = eqToHom rfl := sorry

/-- The module-sheaf pseudofunctor on algebraic spaces over `S`, retaining its pullback
functors. -/
noncomputable def descentPseudofunctor (S : Scheme.{u}) :
    Pseudofunctor (LocallyDiscrete (AlgebraicSpace S)ᵒᵖ) Cat.{u + 1, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of X.unop.Modules)
    (fun f ↦ (pullback f.unop).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (SmallEtaleModuleGlueing.modulesPullbackId X.unop))
    (fun f g ↦ Cat.Hom.isoMk (pullbackComp g.unop f.unop).symm)
    descentPseudofunctor_map₂_associator
    descentPseudofunctor_map₂_leftUnitor
    descentPseudofunctor_map₂_rightUnitor

/-- The fibre of `descentPseudofunctor` over an algebraic space is its category of module
sheaves. -/
theorem descentPseudofunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (descentPseudofunctor S).obj (.mk (.op X)) = Cat.of X.Modules := sorry

/-- The action of `descentPseudofunctor` on a morphism of algebraic spaces is module
pullback. -/
theorem descentPseudofunctor_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ((descentPseudofunctor S).map f.op.toLoc).toFunctor = pullback f := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
