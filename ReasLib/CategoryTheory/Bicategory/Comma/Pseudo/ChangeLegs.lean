/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.ChangeLegs.Pseudofunctor.Basic
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.ChangeLegs.Computations
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.ChangeLegs.Target

/-!
# Change of pseudo comma legs

This is the public entry point for pseudofunctorial change of the two legs of
a pseudo comma bicategory. Import the focused leaves for a smaller dependency
surface when only the explicit data or only the pseudofunctor assembly is
needed. `Pseudo.ChangeLegs.Target` specializes the action to an equivalence of
common target pseudofunctors.
-/
