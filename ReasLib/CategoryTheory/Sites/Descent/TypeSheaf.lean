/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Effective descent for `Type`-valued localized sheaves

This leaf owns the stack-level descent interface for the pseudofunctor that
sends an object of a site to the category of `Type`-valued sheaves on its
slice site. The API is intentionally stated at the stack and fixed-cover
levels, rather than exposing a construction-specific glueing implementation.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.GrothendieckTopology.PseudofunctorOver

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C) {U : C}
variable [UnivLE.{max u v, w}]

/-- `04TR`: the pseudofunctor of `Type`-valued sheaves on localized sites is
a stack for the given Grothendieck topology. -/
@[stacks 04TR "stack"]
theorem isStack :
    (J.pseudofunctorOver (Type w)).IsStack J := sorry

/-- Typeclass access to effective descent for localized `Type`-valued
sheaves. -/
@[stacks 04TR "stack"]
instance instIsStack :
    (J.pseudofunctorOver (Type w)).IsStack J :=
  isStack J

/-- Effective descent for the presieve formed by the arrows of a chosen
covering family. -/
@[stacks 04TR "fixed cover"]
theorem isStackFor_cover (T : J.Cover U) :
    (J.pseudofunctorOver (Type w)).IsStackFor
      (Presieve.ofArrows (fun I : T.Arrow ↦ I.Y) fun I ↦ I.f) := sorry

/-- The descent-data functor for a chosen cover is an equivalence. -/
@[stacks 04TS "fixed cover"]
theorem toDescentData_isEquivalence (T : J.Cover U) :
    ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : T.Arrow ↦ I.f)).IsEquivalence := sorry

/-- The descent-data functor for a chosen cover is essentially surjective. -/
@[stacks 04TR "fixed cover"]
theorem toDescentData_essSurj (T : J.Cover U) :
    ((J.pseudofunctorOver (Type w)).toDescentData
      (fun I : T.Arrow ↦ I.f)).EssSurj := sorry

end CategoryTheory.GrothendieckTopology.PseudofunctorOver
