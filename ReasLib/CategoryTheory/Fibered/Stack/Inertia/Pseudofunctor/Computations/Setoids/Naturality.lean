module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Setoids.Coherence

/-!
# Naturality computations for setoid-stack inertia

This file records naturality of forgetting and of the identity section, including their
ordinary-pseudofunctor `2`-cell equations.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Setoids.inertia

/-- Setoid-stack inertia maps commute with forgetting the selected automorphism. -/
@[simp]
theorem forget.naturality
    {X Y : StackOver.Setoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    map F ≫ forget Y = forget X ≫ F := sorry

/-- Setoid-stack inertia maps carry the identity section to the identity section. -/
@[simp]
theorem identitySection.naturality
    {X Y : StackOver.Setoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    F ≫ identitySection Y = identitySection X ≫ map F := sorry

end StackOver.Setoids.inertia

namespace StackOver.Setoids.Inertia.pseudofunctor

namespace forget

variable {X Y : StackOver.Setoids.{u, v, max w vS, vS} J}

/-- Naturality of setoid-stack inertia forgetting on the ordinary pseudofunctor. -/
@[simp]
theorem naturality (F : X ⟶ Y) :
    (StackOver.Setoids.Inertia.pseudofunctor J).map F ≫
        StackOver.Setoids.inertia.forget Y =
      StackOver.Setoids.inertia.forget X ≫ F := sorry

/-- Setoid-stack inertia forgetting is natural in source `2`-morphisms. -/
theorem naturality₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackOver.Setoids.Inertia.pseudofunctor J).map₂ eta ▷
        StackOver.Setoids.inertia.forget Y =
      eqToHom (naturality F) ≫ StackOver.Setoids.inertia.forget X ◁ eta ≫
        eqToHom (naturality G).symm := sorry

end forget

namespace identitySection

variable {X Y : StackOver.Setoids.{u, v, max w vS, vS} J}

/-- Naturality of the setoid-stack inertia identity section. -/
@[simp]
theorem naturality (F : X ⟶ Y) :
    (Pseudofunctor.id
        (StackOver.Setoids.{u, v, max w vS, vS} J)).map F ≫
          StackOver.Setoids.inertia.identitySection Y =
      StackOver.Setoids.inertia.identitySection X ≫
        (StackOver.Setoids.Inertia.pseudofunctor J).map F := sorry

/-- The ambient cell of the setoid-stack inertia identity section is natural in source
`2`-morphisms. -/
theorem naturality₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackOver.Setoids.inertia.identitySection X ◁
        (StackOver.Setoids.Inertia.pseudofunctor J).map₂ eta).hom =
      (eqToHom (naturality F).symm).hom ≫
        (eta ▷ StackOver.Setoids.inertia.identitySection Y).hom ≫
          (eqToHom (naturality G)).hom := sorry

end identitySection

end StackOver.Setoids.Inertia.pseudofunctor

end CategoryTheory
