module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale.BaseChange
import StacksCheckRecall

/-!
# Base change of rig-étale morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

universe u

/- Lemma 88.20.5: let `S` be a scheme, and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` is
rig-étale and `g` is adic, i.e. `AlgebraicSpace.representableByAlgebraicSpaces g`
in the sense of Definition 87.23.2, then the base change `X ×_Y Z ⟶ Z`, i.e.
`pullback.snd f g`, is rig-étale. -/
@[stacks 0GD1] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigEtale.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [RigEtale f]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g)
    [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)],
    RigEtale (pullback.snd f g))

/- If `IsPullback fst snd f g`, `f` is rig-étale, and `g` is adic, i.e.
`AlgebraicSpace.representableByAlgebraicSpaces g`, then the base-change leg
`snd` is rig-étale. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.RigEtale.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [RigEtale f]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g),
    RigEtale snd)
