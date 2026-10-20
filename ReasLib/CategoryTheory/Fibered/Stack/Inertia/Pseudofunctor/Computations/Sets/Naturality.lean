/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Inertia.Pseudofunctor.Computations.Sets.Coherence

/-!
# Naturality computations for set-stack inertia

Named `1`- and `2`-cell naturality equations for inertia forgetting and the identity section.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets.inertia

/-- Set-stack inertia maps commute with forgetting the selected automorphism. -/
@[simp]
theorem forget.naturality
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    map F ≫ forget Y = forget X ≫ F := sorry

/-- Set-stack inertia maps carry the identity section to the identity section. -/
@[simp]
theorem identitySection.naturality
    {X Y : StackOver.Sets.{u, v, max w vS, vS} J} (F : X ⟶ Y) :
    F ≫ identitySection Y = identitySection X ≫ map F := sorry

end StackOver.Sets.inertia

namespace StackOver.Sets.Inertia.pseudofunctor.forget

variable {X Y : StackOver.Sets.{u, v, max w vS, vS} J}

/-- Naturality of set-stack inertia forgetting on the ordinary pseudofunctor. -/
@[simp]
theorem naturality (F : X ⟶ Y) :
    (StackOver.Sets.Inertia.pseudofunctor J).map F ≫
        StackOver.Sets.inertia.forget Y =
      StackOver.Sets.inertia.forget X ≫ F := sorry

/-- The ambient cell of set-stack inertia forgetting is natural in source `2`-morphisms. -/
theorem naturality₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    ((StackOver.Sets.Inertia.pseudofunctor J).map₂ eta ▷
        StackOver.Sets.inertia.forget Y).hom =
      (eqToHom (naturality F)).hom ≫
        (StackOver.Sets.inertia.forget X ◁ eta).hom ≫
          (eqToHom (naturality G).symm).hom := sorry

end StackOver.Sets.Inertia.pseudofunctor.forget

namespace StackOver.Sets.Inertia.pseudofunctor.identitySection

variable {X Y : StackOver.Sets.{u, v, max w vS, vS} J}

/-- Naturality of the set-stack inertia identity section. -/
@[simp]
theorem naturality (F : X ⟶ Y) :
    (Pseudofunctor.id
        (StackOver.Sets.{u, v, max w vS, vS} J)).map F ≫
          StackOver.Sets.inertia.identitySection Y =
      StackOver.Sets.inertia.identitySection X ≫
        (StackOver.Sets.Inertia.pseudofunctor J).map F := sorry

/-- The ambient cell of the set-stack inertia identity section is natural in source
`2`-morphisms. -/
theorem naturality₂ {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackOver.Sets.inertia.identitySection X ◁
        (StackOver.Sets.Inertia.pseudofunctor J).map₂ eta).hom =
      (eqToHom (naturality F).symm).hom ≫
        (eta ▷ StackOver.Sets.inertia.identitySection Y).hom ≫
          (eqToHom (naturality G)).hom := sorry

end StackOver.Sets.Inertia.pseudofunctor.identitySection

end CategoryTheory
