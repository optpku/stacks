/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RationalMap.Over
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

/- Definition 29.49.1 (1): two partial maps are equivalent exactly when they determine the same
rational map. -/
@[stacks 01RS] #check
  (AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} {f g : X.PartialMap Y},
      f.toRationalMap = g.toRationalMap ↔ f.equiv g)

/- Definition 29.49.1 (2): every rational map has a partial-map representative. -/
@[stacks 01RS] #check
  (AlgebraicGeometry.Scheme.RationalMap.exists_rep :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (φ : X ⤏ Y),
      ∃ f : X.PartialMap Y, f.toRationalMap = φ)

/- Definition 29.49.1 (3): a rational map between schemes over `S` is over `S` exactly when it
has a partial-map representative over `S`. -/
@[stacks 01RS] #check
  (AlgebraicGeometry.Scheme.RationalMap.isOver_iff_exists_partialMap_over :
    ∀ {S X Y : AlgebraicGeometry.Scheme.{u}} [X.Over S] [Y.Over S] (φ : X ⤏ Y),
      φ.IsOver S ↔ ∃ f : X.PartialMap Y, f.IsOver S ∧ f.toRationalMap = φ)
