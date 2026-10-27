/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flattening.InDimensions
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# The flat-in-dimensions functor on schemes over the base scheme

The base changes on which a module is flat in dimensions at least `n` define a
subfunctor of the functor of points of its target algebraic space.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flattening

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (ℱ : X.Modules)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (n : ℕ)

/-- The subfunctor of the functor of points of `Y` consisting of morphisms along
which the pullback of `ℱ` is flat over the test scheme in dimensions at least `n`. -/
def flatInDimensionsOverSSubfunctor : Subfunctor Y.functorOfPoints where
  obj T := {φ | let a : ofOver T.unop ⟶ Y := yonedaEquiv.symm φ;
    Modules.flatOverInDimensionsGE
      (Modules.baseChangeModule f a ℱ) (pullback.snd f a) n}
  map := sorry

/-- Membership in the flat-in-dimensions subfunctor is flatness of the pullback
module over the test scheme in dimensions at least `n`. -/
theorem mem_flatInDimensionsOverSSubfunctor {T : Over S}
    (φ : Y.functorOfPoints.obj (op T)) :
    φ ∈ (flatInDimensionsOverSSubfunctor f ℱ n).obj (op T) ↔
      (let a : ofOver T ⟶ Y := yonedaEquiv.symm φ;
        Modules.flatOverInDimensionsGE
          (Modules.baseChangeModule f a ℱ) (pullback.snd f a) n) :=
  Iff.rfl

/-- The functor on schemes over `S` recording morphisms to `Y` along which the
pullback of `ℱ` is flat in dimensions at least `n`. -/
def flatInDimensionsOverSFunctor : (Over S)ᵒᵖ ⥤ Type u :=
  (flatInDimensionsOverSSubfunctor f ℱ n).toFunctor

/-- The inclusion of the flat-in-dimensions functor into the functor of points of `Y`. -/
def flatInDimensionsOverSFunctor_toY :
    flatInDimensionsOverSFunctor f ℱ n ⟶ Y.functorOfPoints :=
  (flatInDimensionsOverSSubfunctor f ℱ n).ι

/-- A scheme `T` over `S` has a flat-in-dimensions point if and only if some
morphism from `T` to `Y` makes the pullback of `ℱ` flat in dimensions at least `n`. -/
theorem flatInDimensionsOverSFunctor_nonempty_iff (T : Over S) :
    Nonempty ((flatInDimensionsOverSFunctor f ℱ n).obj (op T)) ↔
      ∃ a : ofOver T ⟶ Y, Modules.flatOverInDimensionsGE
        (Modules.baseChangeModule f a ℱ) (pullback.snd f a) n :=
  sorry

namespace flatInDimensionsOverSFunctor

/-- The algebraic space with the flat-in-dimensions functor as its functor of
points, provided that functor satisfies the algebraic-space conditions. -/
def space [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)] : AlgebraicSpace S :=
  ofIsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)

/-- The structural morphism from the flat-in-dimensions space to `Y`, induced
by the subfunctor inclusion. -/
def toY [IsAlgebraicSpace (flatInDimensionsOverSFunctor f ℱ n)] :
    space f ℱ n ⟶ Y :=
  flatInDimensionsOverSFunctor_toY f ℱ n

end flatInDimensionsOverSFunctor

end AlgebraicGeometry.AlgebraicSpace.Flattening
