/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_25_1_Surjective
public import stacks_project.Chap87.Lemma_87_24_4_Pullback
public import stacks_project.Chap88.Definition_88_13_4

/-!
# Base change of flat morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Flat

/-- Lemma 88.13.6 (1): let `S` be a scheme, and let `f : X ⟶ Y` and
`g : Z ⟶ Y` be morphisms of locally Noetherian formal algebraic spaces
over `S`. If `f` is flat and `g_red : Z_red ⟶ Y_red`, i.e.
`mapReduction g`, is locally of finite type as a morphism of algebraic
spaces, then the base change `X ×_Y Z ⟶ Z`, i.e. `pullback.snd f g`,
is flat. -/
@[stacks 0GCE]
instance pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [Reduction Y] [Reduction Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [Flat f]
    [AlgebraicSpace.LocallyOfFiniteType (mapReduction g)]
    [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)] :
    Flat (pullback.snd f g) :=
  sorry

/-- If `IsPullback fst snd f g`, `f` is flat, and `mapReduction g` is
locally of finite type as a morphism of algebraic spaces, then the
base-change leg `snd` is flat. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    [Reduction Y] [Reduction Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [Flat f]
    [AlgebraicSpace.LocallyOfFiniteType (mapReduction g)] :
    Flat snd :=
  sorry

/-- Lemma 88.13.6 (2): let `S` be a scheme, and let `f : X ⟶ Y` and
`g : Z ⟶ Y` be morphisms of locally Noetherian formal algebraic spaces
over `S`. If `f` is flat and locally of finite type, then the base change
`X ×_Y Z ⟶ Z`, i.e. `pullback.snd f g`, is flat and locally of finite
type. The locally-of-finite-type conjunct is
`locallyOfFiniteType_pullback_snd`. -/
@[stacks 0GCE]
theorem pullback_snd_flat_and_locallyOfFiniteType
    {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [Flat f]
    [LocallyOfFiniteType f] [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)] :
    Flat (pullback.snd f g) ∧ LocallyOfFiniteType (pullback.snd f g) :=
  sorry

/-- The base-change projection `pullback.snd f g` of a flat, locally of
finite type morphism of locally Noetherian formal algebraic spaces is
flat. -/
instance pullback_snd_of_locallyOfFiniteType
    {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [Flat f]
    [LocallyOfFiniteType f] [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)] :
    Flat (pullback.snd f g) :=
  sorry

/-- If `IsPullback fst snd f g` and `f` is flat and locally of finite
type, then the base-change leg `snd` is flat. -/
theorem of_isPullback_of_locallyOfFiniteType
    {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [Flat f] [LocallyOfFiniteType f] :
    Flat snd :=
  sorry

end Flat

end AlgebraicGeometry.FormalAlgebraicSpace
