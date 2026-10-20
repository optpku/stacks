/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle
public import Mathlib.Tactic.Recall

/-!
# Definition 31.31.6

The reusable projective-bundle owner is maintained in
`ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle`.
-/

/- Definition 31.31.6: a projective bundle represents invertible quotients of the pullback of
its defining module. -/
recall CategoryTheory.InvertibleQuotient
recall AlgebraicGeometry.Scheme.ProjectiveBundle.Lift
recall AlgebraicGeometry.Scheme.ProjectiveBundle.Representation
recall AlgebraicGeometry.Scheme.ProjectiveBundle.Representation.liftEquiv
recall AlgebraicGeometry.Scheme.ProjectiveBundle.Representation.isSeparated
recall AlgebraicGeometry.Scheme.ProjectiveBundle.sectionLiftEquiv
recall AlgebraicGeometry.Scheme.ProjectiveBundle.sectionQuotient
