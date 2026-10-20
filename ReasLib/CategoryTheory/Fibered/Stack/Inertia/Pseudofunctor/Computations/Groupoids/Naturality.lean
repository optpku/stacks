module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Groupoids.Coherence

/-!
# Naturality computations for groupoid-stack inertia

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

namespace StackOver.Groupoids.inertia

/-- Groupoid-stack inertia maps commute with forgetting the selected automorphism. -/
@[simp]
theorem forget.naturality
    {X Y : StackOver.Groupoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    map F ≫ forget Y = forget X ≫ F := sorry

/-- Groupoid-stack inertia maps carry the identity section to the identity section. -/
@[simp]
theorem identitySection.naturality
    {X Y : StackOver.Groupoids.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    F ≫ identitySection Y = identitySection X ≫ map F := sorry

end StackOver.Groupoids.inertia

namespace StackOver.Groupoids.Inertia.pseudofunctor

namespace forget

variable {X Y : StackOver.Groupoids.{u, v, max w vS, vS} J}

/-- Naturality of groupoid-stack inertia forgetting on the ordinary pseudofunctor. -/
@[simp]
theorem naturality (F : X ⟶ Y) :
    (StackOver.Groupoids.Inertia.pseudofunctor J).map F ≫
        StackOver.Groupoids.inertia.forget Y =
      StackOver.Groupoids.inertia.forget X ≫ F := sorry

/-- Groupoid-stack inertia forgetting is natural in source `2`-morphisms. -/
theorem naturality₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackOver.Groupoids.Inertia.pseudofunctor J).map₂ eta ▷
        StackOver.Groupoids.inertia.forget Y =
      eqToHom (naturality F) ≫ StackOver.Groupoids.inertia.forget X ◁ eta ≫
        eqToHom (naturality G).symm := sorry

end forget

namespace identitySection

variable {X Y : StackOver.Groupoids.{u, v, max w vS, vS} J}

/-- Naturality of the groupoid-stack inertia identity section. -/
@[simp]
theorem naturality (F : X ⟶ Y) :
    (Pseudofunctor.id
        (StackOver.Groupoids.{u, v, max w vS, vS} J)).map F ≫
          StackOver.Groupoids.inertia.identitySection Y =
      StackOver.Groupoids.inertia.identitySection X ≫
        (StackOver.Groupoids.Inertia.pseudofunctor J).map F := sorry

/-- The groupoid-stack inertia identity section is natural in source `2`-morphisms. -/
theorem naturality₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    StackOver.Groupoids.inertia.identitySection X ◁
        (StackOver.Groupoids.Inertia.pseudofunctor J).map₂ eta =
      eqToHom (naturality F).symm ≫
        eta ▷ StackOver.Groupoids.inertia.identitySection Y ≫
          eqToHom (naturality G) := sorry

end identitySection

end StackOver.Groupoids.Inertia.pseudofunctor

end CategoryTheory
