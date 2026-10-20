/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve.Contraction.Stein
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Scheme.Hom.FiniteType (QuasiFiniteAt)
open scoped AlgebraicGeometry

universe u

/- Lemma 54.16.4: if a proper morphism from a Noetherian scheme maps an exceptional curve of
the first kind to one point and is quasi-finite away from that curve, then the first map in its
canonical Stein factorization is a contraction whose center lies over that point. -/
@[stacks 0C2L] #check (AlgebraicGeometry.IsExceptionalCurveFirstKind.exists_isContraction_toNormalization :
  ∀ {X Y : Scheme.{u}} [IsNoetherian X]
    (E : X.IdealSheafData) [IsExceptionalCurveFirstKind E]
    (f : X ⟶ Y) [IsNoetherian Y] [IsProper f] (y : Y),
    Set.MapsTo f E.support ({y} : Set Y) →
    (∀ x : X, x ∉ E.support → QuasiFiniteAt f x) →
    ∃ y' : closedPoints f.normalization,
      IsContraction E f.toNormalization y' ∧
        f.fromNormalization y'.1 = y)
