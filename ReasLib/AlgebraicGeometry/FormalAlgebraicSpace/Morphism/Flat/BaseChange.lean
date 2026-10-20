/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType.BaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Base change of flat morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.Flat

/-- In a cartesian square of locally Noetherian formal algebraic spaces, the
base change of a flat morphism is flat if the induced morphism on reductions
is locally of finite type. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    (RY : ReductionData Y) (RZ : ReductionData Z)
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [Flat f]
    [AlgebraicSpace.LocallyOfFiniteType (RZ.map RY g)] :
    Flat snd :=
  sorry

/-- The pullback projection of a flat morphism of locally Noetherian formal
algebraic spaces is flat if the base-changing morphism induces a locally
of finite type morphism on reductions. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (RY : ReductionData Y) (RZ : ReductionData Z)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [Flat f]
    [AlgebraicSpace.LocallyOfFiniteType (RZ.map RY g)]
    [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)] :
    Flat (pullback.snd f g) := by
  exact of_isPullback RY RZ (IsPullback.of_hasPullback f g)

/-- In a cartesian square of locally Noetherian formal algebraic spaces,
the base change of a flat, locally of finite type morphism is flat. -/
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

/-- The pullback projection of a flat, locally of finite type morphism
of locally Noetherian formal algebraic spaces is flat. -/
instance pullback_snd_of_locallyOfFiniteType
    {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [Flat f]
    [LocallyOfFiniteType f] [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)] :
    Flat (pullback.snd f g) := by
  exact of_isPullback_of_locallyOfFiniteType (IsPullback.of_hasPullback f g)

/-- The pullback projection of a flat, locally of finite type morphism
of locally Noetherian formal algebraic spaces is flat and locally of finite type. -/
theorem pullback_snd_flat_and_locallyOfFiniteType
    {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [Flat f]
    [LocallyOfFiniteType f] [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)] :
    Flat (pullback.snd f g) ∧ LocallyOfFiniteType (pullback.snd f g) := by
  exact ⟨pullback_snd_of_locallyOfFiniteType f g, LocallyOfFiniteType.instPullbackSnd f g⟩

end AlgebraicGeometry.FormalAlgebraicSpace.Flat
