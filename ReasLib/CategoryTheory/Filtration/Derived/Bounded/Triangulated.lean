/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.Bounded.Relations
public import ReasLib.CategoryTheory.Filtration.Derived.Triangulated
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Triangulated structure on bounded finite filtered derived categories

The boundedness properties are inverse images of the canonical `t`-structure properties under the
derived associated-graded functor.  Once the exactness instance for that functor is in scope,
Mathlib supplies the full-subcategory shift and triangulated structures automatically.  This leaf
assembles the required imports and checks that clients need no local `letI` pins or duplicate
instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

-- These are all canonical `ObjectProperty.inverseImage` and full-subcategory instances.
#synth (Plus.property C h_inverts).IsTriangulated
#synth (Minus.property C h_inverts).IsTriangulated
#synth (Bounded.property C h_inverts).IsTriangulated

#synth Pretriangulated (Plus.Category C h_inverts)
#synth Pretriangulated (Minus.Category C h_inverts)
#synth Pretriangulated (Bounded.Category C h_inverts)

#synth IsTriangulated (Plus.Category C h_inverts)
#synth IsTriangulated (Minus.Category C h_inverts)
#synth IsTriangulated (Bounded.Category C h_inverts)

end CategoryTheory.FilteredObject.FiniteDerived
