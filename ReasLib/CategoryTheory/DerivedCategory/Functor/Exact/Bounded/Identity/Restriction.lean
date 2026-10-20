/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Identity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity comparisons for restricted exact derived functors

The ambient identity comparison for exact derived functors restricts to any
full subcategory whose object property is preserved by the bundled exact
identity.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.FullSubcategory

noncomputable section

universe w v u

namespace CategoryTheory.ExactFunctor.Derived.Restriction

variable (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A]

/-- Restrict the ambient exact-derived identity comparison to an arbitrary
object property preserved by the bundled exact identity. -/
@[stacks 015F "identity comparison for property-restricted exact derived functors"]
noncomputable def idFunctorIso
    (P : ObjectProperty (DerivedCategory A))
    (h : P ≤ P.inverseImage (ExactFunctor.id A).mapDerivedCategory) :
    restrict (ExactFunctor.id A).mapDerivedCategory h ≅
      Functor.id P.FullSubcategory :=
  restrict.natIso h (restrict.mapsToId P)
      (ExactFunctor.MapDerivedCategory.idFunctorIso A) ≪≫
    restrict.idIso P

end CategoryTheory.ExactFunctor.Derived.Restriction
