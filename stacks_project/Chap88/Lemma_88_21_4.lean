/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_21_1

/-!
# Base change of rig-surjective morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace RigSurjective

/-- Lemma 88.21.4: let `S` be a scheme, and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of formal algebraic spaces over `S`. Assume `X`, `Y`, `Z` are locally
Noetherian and that `f` and `g` are locally of finite type. If `f` is
rig-surjective, then the base change `Z ×_Y X ⟶ Z`, realized as
`pullback.snd f g : pullback f g ⟶ Z` up to the canonical symmetry of fibre
products, is rig-surjective. -/
@[stacks 0AQS]
instance pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] [RigSurjective f]
    [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)]
    [LocallyOfFiniteType (pullback.snd f g)] :
    RigSurjective (pullback.snd f g) :=
  sorry

/-- If `IsPullback fst snd f g`, `f` is rig-surjective, and `f`, `g`, and `snd`
are locally of finite type, then the base-change leg `snd` is rig-surjective. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] [RigSurjective f] [LocallyOfFiniteType snd] :
    RigSurjective snd :=
  sorry

end RigSurjective

end AlgebraicGeometry.FormalAlgebraicSpace
