/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSmooth.BaseChange
import StacksCheckRecall

/-!
# Base change of rig-smooth morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 88.18.3: let `S` be a scheme, and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` is
rig-smooth and `g` is adic, i.e. `AlgebraicSpace.representableByAlgebraicSpaces g`
in the sense of Definition 87.23.2, then the base change `X ×_Y Z ⟶ Z`, i.e.
`pullback.snd f g`, is rig-smooth. -/
@[stacks 0GCR] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [RigSmooth f]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g)
    [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)],
    RigSmooth (pullback.snd f g))

/- If `IsPullback fst snd f g`, `f` is rig-smooth, and `g` is adic, i.e.
`AlgebraicSpace.representableByAlgebraicSpaces g`, then the base-change leg
`snd` is rig-smooth. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [RigSmooth f]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g),
    RigSmooth snd)
