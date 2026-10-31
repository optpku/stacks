/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedQuasiIso
public import ReasLib.CategoryTheory.ObjectProperty.Retract.InverseImage
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangulated calculus for bounded finite filtered quasi-isomorphisms

The bounded acyclic properties are the triangulated subcategories underlying the three restricted
Verdier morphism properties.  This leaf registers the standard calculus-of-fractions instances;
clients of the bounded localizations therefore do not need to rebuild these proof-level inputs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty CategoryTheory.MorphismProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace Plus.QuasiIso

/-- Bounded-below finite filtered quasi-isomorphisms form a saturated multiplicative system. -/
@[stacks 05S6 "bounded-below finite filtered quasi-isomorphism"]
instance isSaturated :
    (Plus.QuasiIso C).IsSaturatedMultiplicativeSystem := sorry

/-- Bounded-below finite filtered quasi-isomorphisms are compatible with triangulation. -/
@[stacks 05S6 "bounded-below finite filtered quasi-isomorphism"]
instance compatibleWithTriangulation :
    (Plus.QuasiIso C).IsCompatibleWithTriangulation := sorry

end Plus.QuasiIso

namespace Minus.QuasiIso

/-- Bounded-above finite filtered quasi-isomorphisms form a saturated multiplicative system. -/
@[stacks 05S6 "bounded-above finite filtered quasi-isomorphism"]
instance isSaturated :
    (Minus.QuasiIso C).IsSaturatedMultiplicativeSystem := sorry

/-- Bounded-above finite filtered quasi-isomorphisms are compatible with triangulation. -/
@[stacks 05S6 "bounded-above finite filtered quasi-isomorphism"]
instance compatibleWithTriangulation :
    (Minus.QuasiIso C).IsCompatibleWithTriangulation := sorry

end Minus.QuasiIso

namespace Bounded.QuasiIso

/-- Bounded finite filtered quasi-isomorphisms form a saturated multiplicative system. -/
@[stacks 05S6 "bounded finite filtered quasi-isomorphism"]
instance isSaturated :
    (Bounded.QuasiIso C).IsSaturatedMultiplicativeSystem := sorry

/-- Bounded finite filtered quasi-isomorphisms are compatible with triangulation. -/
@[stacks 05S6 "bounded finite filtered quasi-isomorphism"]
instance compatibleWithTriangulation :
    (Bounded.QuasiIso C).IsCompatibleWithTriangulation := sorry

end Bounded.QuasiIso

end CategoryTheory.FilteredObject.FiniteDerived
