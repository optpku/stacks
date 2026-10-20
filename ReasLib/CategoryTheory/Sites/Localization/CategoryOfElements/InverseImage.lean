/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Localization.CategoryOfElements
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse image for category-of-elements localizations

This leaf gives a short, coefficient-independent name to restriction along the
category-of-elements projection.  More specialized exactness, injectivity, and cohomology
properties are layered on this owner in separate files.
-/

@[expose] public section

open CategoryTheory

universe u v w z

namespace CategoryTheory.Sheaf.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Inverse image along the category-of-elements localization of `K`, with values in `A`. -/
@[stacks 07A0 "category-of-elements inverse image"]
abbrev inverseImage (K : Sheaf J (Type v)) (A : Type w) [Category.{z} A] :
    Sheaf J A ⥤ Sheaf (localizationTopology K) A :=
  (localizationProjection K).sheafPushforwardContinuous A (localizationTopology K) J

end CategoryTheory.Sheaf.Localization
