/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Basic.Coherence

/-!
# Naturality computations for stack inertia

Naturality of the forgetful and identity-section transformations on `1`- and `2`-morphisms.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.inertia

/-- Bundled stack inertia maps commute with forgetting the selected automorphism. -/
@[simp]
theorem forget.naturality
    {X Y : StackOver.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    map F ≫ forget Y = forget X ≫ F := sorry

/-- Stack inertia maps carry the identity section to the identity section. -/
@[simp]
theorem identitySection.naturality
    {X Y : StackOver.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    F ≫ identitySection Y = identitySection X ≫ map F := sorry

end StackOver.inertia

namespace StackOver.Inertia.pseudofunctor

namespace forget

variable {X Y : StackOver.{u, v, max w vS, vS} J}

/-- Naturality of stack inertia forgetting, stated on the ordinary pseudofunctor. -/
@[simp]
theorem naturality (F : X ⟶ Y) :
    (StackOver.Inertia.pseudofunctor J).map F ≫ StackOver.inertia.forget Y =
      StackOver.inertia.forget X ≫ F := sorry

/-- Stack inertia forgetting is natural in source `2`-morphisms. -/
theorem naturality₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackOver.Inertia.pseudofunctor J).map₂ eta ▷ StackOver.inertia.forget Y =
      eqToHom (naturality F) ≫ StackOver.inertia.forget X ◁ eta ≫
        eqToHom (naturality G).symm := sorry

end forget

namespace identitySection

variable {X Y : StackOver.{u, v, max w vS, vS} J}

/-- Naturality of the stack inertia identity section, stated on the ordinary pseudofunctor. -/
@[simp]
theorem naturality (F : X ⟶ Y) :
    (Pseudofunctor.id (StackOver.{u, v, max w vS, vS} J)).map F ≫
        StackOver.inertia.identitySection Y =
      StackOver.inertia.identitySection X ≫
        (StackOver.Inertia.pseudofunctor J).map F := sorry

/-- The stack inertia identity section is natural in source `2`-morphisms. -/
theorem naturality₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    StackOver.inertia.identitySection X ◁
        (StackOver.Inertia.pseudofunctor J).map₂ eta =
      eqToHom (naturality F).symm ≫
        eta ▷ StackOver.inertia.identitySection Y ≫
          eqToHom (naturality G) := sorry

end identitySection

end StackOver.Inertia.pseudofunctor

end CategoryTheory
