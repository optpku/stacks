/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigFlat.BaseChange
import StacksCheckRecall

/-!
# Base change of rig-flat morphisms of locally Noetherian formal algebraic spaces
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

universe u

/- Lemma 88.16.3: let `S` be a scheme, and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` is
rig-flat and `g` is locally of finite type, then the base change
`X ×_Y Z ⟶ Z`, i.e. `pullback.snd f g`, is rig-flat. -/
@[stacks 0GGZ] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigFlat.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [RigFlat f]
    [LocallyOfFiniteType g], RigFlat (pullback.snd f g))

/- If `IsPullback fst snd f g`, `f` is rig-flat, and `g` is locally of finite
type, then the base-change leg `snd` is rig-flat. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.RigFlat.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [RigFlat f] [LocallyOfFiniteType g], RigFlat snd)

