/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Fibered.InSetoids.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebraic-space representability and fiberwise isomorphism classes

A category fibred in groupoids over `(Sch/S)_fppf` is representable by an algebraic
space exactly when it is fibred in setoids and its presheaf of fiberwise isomorphism
classes is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A category fibred in groupoids over `(Sch/S)_fppf` is representable by an
algebraic space over `S` if and only if it is fibred in setoids and its presheaf
of fiberwise isomorphism classes is naturally isomorphic to the universe lift
of the functor of points of an algebraic space over `S`. -/
@[stacks 02ZX]
theorem IsRepresentableByAlgebraicSpace.iff_inSetoids_and_fiberClasses
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    IsRepresentableByAlgebraicSpace X ↔
      Functor.IsFibered.InSetoids X.p ∧
        ∃ F : AlgebraicSpace S,
          Nonempty
            (Functor.fiberIsoClassPresheaf X.p ≅
              F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  sorry

/-- A category fibred in groupoids representable by an algebraic space is fibred in
setoids. -/
theorem IsRepresentableByAlgebraicSpace.inSetoids
    {S : Scheme.{u}} {X : GroupoidsOver S}
    (hX : IsRepresentableByAlgebraicSpace X) :
    Functor.IsFibered.InSetoids X.p :=
  sorry

/-- The fiberwise-isomorphism-class presheaf of a category fibred in groupoids
representable by an algebraic space is naturally isomorphic, after universe lift, to
the functor of points of some algebraic space. -/
theorem IsRepresentableByAlgebraicSpace.fiberClasses
    {S : Scheme.{u}} {X : GroupoidsOver S}
    (hX : IsRepresentableByAlgebraicSpace X) :
    ∃ F : AlgebraicSpace S,
      Nonempty
        (Functor.fiberIsoClassPresheaf X.p ≅
          F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  sorry

/-- A category fibred in groupoids is representable by an algebraic space once it is
fibred in setoids and its fiberwise-isomorphism-class presheaf matches an algebraic
space after universe lift. -/
theorem IsRepresentableByAlgebraicSpace.of_inSetoids_of_fiberClasses
    {S : Scheme.{u}} {X : GroupoidsOver S}
    (hSetoids : Functor.IsFibered.InSetoids X.p)
    (hClasses :
      ∃ F : AlgebraicSpace S,
        Nonempty
          (Functor.fiberIsoClassPresheaf X.p ≅
            F.functorOfPoints ⋙ uliftFunctor.{u + 1, u})) :
    IsRepresentableByAlgebraicSpace X :=
  sorry

end AlgebraicGeometry
