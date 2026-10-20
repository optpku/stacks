/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.CategoryTheory.Sites.Cech.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additivity of Cech complexes

Additivity of the coefficient functor is independent of exactness of products.  Keeping this
instance in its own leaf lets homology and other additive constructions use a Cech complex in a
general preadditive coefficient category without importing exactness hypotheses.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe w vA uA v u

namespace CategoryTheory.Cech

variable {C : Type u} [Category.{v} C]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]

section Base

variable [HasFiniteProducts C] {ι : Type w} (family : ι → C)
variable [HasProducts.{w} A]

/-- The coefficient-independent Cech-complex functor is additive. -/
@[stacks 00ZY "additivity of the coefficient-independent Cech-complex functor"]
noncomputable instance cechComplexFunctor_additive :
    (cechComplexFunctor family : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ).Additive := sorry

end Base

variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)
variable [HasProducts.{w} A]

/-- The Cech-complex functor is additive in its preadditive presheaf coefficient. -/
@[stacks 00ZY "additivity of the Cech-complex functor"]
noncomputable instance complexFunctorAdditive :
    (cechComplexOnPresheaves U family :
      (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ).Additive := sorry

end CategoryTheory.Cech
