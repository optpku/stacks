/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective
import StacksCheckRecall

/-!
# Composition of rig-surjective morphisms

The composition of locally of finite type rig-surjective morphisms of locally
Noetherian formal algebraic spaces is again rig-surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace

universe u

/- Lemma 88.21.3: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of formal algebraic spaces over `S`. Assume `X`, `Y`, `Z` are locally
Noetherian and `f` and `g` locally of finite type. Then if `f` and `g` are
rig-surjective, so is `g ∘ f`. In Lean composition this is
`RigSurjective f → RigSurjective g → RigSurjective (f ≫ g)`. -/
@[stacks 0AQR] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective.comp :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [RigSurjective f] [RigSurjective g], RigSurjective (f ≫ g))
