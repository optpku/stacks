/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_16_1

/-!
# Base change of rig-flat morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace RigFlat

/-- Lemma 88.16.3: let `S` be a scheme, and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` is
rig-flat and `g` is locally of finite type, then the base change
`X ×_Y Z ⟶ Z`, i.e. `pullback.snd f g`, is rig-flat. -/
@[stacks 0GGZ]
instance pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [RigFlat f]
    [LocallyOfFiniteType g] [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)] :
    RigFlat (pullback.snd f g) :=
  sorry

/-- If `IsPullback fst snd f g`, `f` is rig-flat, and `g` is locally of finite
type, then the base-change leg `snd` is rig-flat. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [RigFlat f] [LocallyOfFiniteType g] :
    RigFlat snd :=
  sorry

end RigFlat

end AlgebraicGeometry.FormalAlgebraicSpace
