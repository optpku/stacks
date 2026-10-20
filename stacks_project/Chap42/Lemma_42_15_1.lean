/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- In the displayed fibre product square, the base change `f'`
of the proper morphism `f` is proper. -/
#check
  (fun {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
      (X Y X' Y' : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      (square : IsPullback g'.left f'.left f.left g.left) (r : ℕ)
      [IsProper f.left] [Flat g.left] [Scheme.Hom.RelativeDimension g.left r] ↦
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback square inferInstance :
      IsProper f'.left))

/- In the displayed fibre product square, the base change `g'`
of the flat morphism `g` is flat. -/
#check
  (fun {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
      (X Y X' Y' : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      (square : IsPullback g'.left f'.left f.left g.left) (r : ℕ)
      [IsProper f.left] [Flat g.left] [Scheme.Hom.RelativeDimension g.left r] ↦
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback square.flip inferInstance :
      Flat g'.left))

/- In the displayed fibre product square, the flat base change
`g'` has the same relative dimension `r` as `g`. -/
#check
  (fun {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
      (X Y X' Y' : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      (square : IsPullback g'.left f'.left f.left g.left) (r : ℕ)
      [IsProper f.left] [Flat g.left] [Scheme.Hom.RelativeDimension g.left r] ↦
    ((Scheme.Hom.instRelativeDimensionIsStableUnderBaseChange r).of_isPullback
        square.flip inferInstance :
      Scheme.Hom.RelativeDimension g'.left r))

/- Lemma 42.15.1: in a fibre product square, properness and flatness of fixed relative
dimension are preserved, and flat pullback commutes with proper pushforward on cycles. -/
@[stacks 02RG] #check
  (AlgebraicGeometry.CycleGroup.flatPullback_map_of_isPullback :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
      (X Y X' Y' : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      (square : IsPullback g'.left f'.left f.left g.left) (r : ℕ)
      [IsProper f.left] [Flat g.left] [Scheme.Hom.RelativeDimension g.left r]
      (k : ℤ) (α : CycleGroup X.left (X.hom.relativeDimensionFunction delta) k),
      letI : IsProper f'.left :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback square inferInstance
      letI : Flat g'.left :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback square.flip inferInstance
      letI : Scheme.Hom.RelativeDimension g'.left r :=
        (Scheme.Hom.instRelativeDimensionIsStableUnderBaseChange r).of_isPullback
          square.flip inferInstance
      AlgebraicGeometry.CycleGroup.flatPullback delta Y' Y g r k
          (AlgebraicGeometry.CycleGroup.mapHom f.left
            (X.hom.relativeDimensionFunction delta)
            (Y.hom.relativeDimensionFunction delta) k α) =
        AlgebraicGeometry.CycleGroup.mapHom f'.left
          (X'.hom.relativeDimensionFunction delta)
          (Y'.hom.relativeDimensionFunction delta) (k + (r : ℤ))
          (AlgebraicGeometry.CycleGroup.flatPullback delta X' X g' r k α))
