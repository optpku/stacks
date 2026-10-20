/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Tower
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Cone
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.DerivedLimit
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.ShortComplex
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Functor
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.IsOf
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Presentation

/-!
# Represented Hom sequences for sequential homotopy colimits

@stack 0CQX

Convenience import for represented Hom towers, the cone and first-derived-limit maps associated
to an explicit telescope presentation, their Milnor short complex, additive target functoriality,
contravariance in presentation morphisms, and the presentation-independent short-exactness
statement.
-/
