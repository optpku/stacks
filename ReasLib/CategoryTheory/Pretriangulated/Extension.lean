/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.Extension.Interval
public import ReasLib.CategoryTheory.Pretriangulated.Extension.Coproduct
public import ReasLib.CategoryTheory.Pretriangulated.Extension.Stage
public import ReasLib.CategoryTheory.Pretriangulated.Extension.Functor
public import ReasLib.CategoryTheory.Pretriangulated.Extension.Supremum

/-!
# Additive Extension Constructions

Convenience import for the reusable object-property API for finite additive
extension stages, their functoriality, and their interaction with suprema.
Import a leaf module when only one of those layers is needed.
-/

open CategoryTheory.ObjectProperty

namespace CategoryTheory.ObjectProperty.ExtensionProductNotation

/-- Scoped notation for the extension product of object properties. -/
scoped notation:70 P:70 " ⋆ " Q:71 => extensionProduct P Q

end CategoryTheory.ObjectProperty.ExtensionProductNotation
