/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Branch
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Structure
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Quotient
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Nagata
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Completion
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Curve.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Curve.Nagata

/-!
# Scheme normalization

Convenience import for the reusable scheme-normalization API.  Applications
that need only stalk constructions or only curve consequences should import
the corresponding narrow leaf instead.
-/
