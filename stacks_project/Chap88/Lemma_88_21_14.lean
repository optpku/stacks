/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace

universe u

/- Lemma 88.21.14 (1): let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. Assume `g` is
locally of finite type, `f` is rig-smooth and rig-surjective, and `g ∘ f` is
rig-smooth. Then `g` is rig-smooth. In Lean composition this is: if `f` is
rig-smooth and rig-surjective and `f ≫ g` is rig-smooth, then so is `g`.
Rig-surjectivity is defined only for locally finite type maps, so
`LocallyOfFiniteType f` is part of the meaning of `RigSurjective f`. -/
@[stacks 0GH6] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth.of_comp_rigSurjective :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [RigSmooth f] [RigSurjective f] [RigSmooth (f ≫ g)],
    RigSmooth g)

/- Lemma 88.21.14 (2): let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. Assume `g` is
locally of finite type, `f` is rig-étale and rig-surjective, and `g ∘ f` is
rig-étale. Then `g` is rig-étale. In Lean composition this is: if `f` is
rig-étale and rig-surjective and `f ≫ g` is rig-étale, then so is `g`.
Rig-surjectivity is defined only for locally finite type maps, so
`LocallyOfFiniteType f` is part of the meaning of `RigSurjective f`. -/
@[stacks 0GH6] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigEtale.of_comp_rigSurjective :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    [RigEtale f] [RigSurjective f] [RigEtale (f ≫ g)],
    RigEtale g)
