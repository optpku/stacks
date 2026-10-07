module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_18_1

/-!
# Base change of rig-smooth morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace RigSmooth

/-- Lemma 88.18.3: let `S` be a scheme, and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` is
rig-smooth and `g` is adic, i.e. `AlgebraicSpace.representableByAlgebraicSpaces g`
in the sense of Definition 87.23.2, then the base change `X ×_Y Z ⟶ Z`, i.e.
`pullback.snd f g`, is rig-smooth. -/
@[stacks 0GCR]
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [RigSmooth f]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g)
    [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)] :
    RigSmooth (pullback.snd f g) :=
  sorry

/-- If `IsPullback fst snd f g`, `f` is rig-smooth, and `g` is adic, i.e.
`AlgebraicSpace.representableByAlgebraicSpaces g`, then the base-change leg
`snd` is rig-smooth. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [RigSmooth f]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g) :
    RigSmooth snd :=
  sorry

end RigSmooth

end AlgebraicGeometry.FormalAlgebraicSpace
