/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import ReasLib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Products
public import ReasLib.CategoryTheory.Limits.Over.Products
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Covering morphisms of formal coproduct families

The covering condition on a morphism of formal coproducts is packaged as a
`MorphismProperty`.  Its fixed-target specialization is the inverse image along the canonical
forgetful functor, so all semantics and multiplicative structure remain owned by the ambient
property.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

namespace SemiRepresentableFamily

namespace Hom

/-- The family over a target component formed by all source components mapping to it. -/
def fiber {K L : Limits.FormalCoproduct.{w} C} (f : K ⟶ L) (j : L.index) :
    OverFamily.{v, u, w} (L.obj j) where
  I := { i : K.index // f.f i = j }
  obj := fun ⟨i, h⟩ ↦ h ▸ CategoryTheory.Over.mk (f.φ i)

end Hom

/-- Definition 25.3.1 (1): the morphism property on formal coproducts whose fiber over every
target component is a covering family for `J`. -/
@[stacks 01G3 "formal-coproduct covering property"]
def covering (J : GrothendieckTopology C) :
    MorphismProperty (Limits.FormalCoproduct.{w} C) :=
  fun {_ L} f ↦ ∀ j : L.index, (Hom.fiber f j).toSieve ∈ J (L.obj j)

/-- Membership in the formal-coproduct covering property is the componentwise fiber condition. -/
@[simp] theorem mem_covering_iff (J : GrothendieckTopology C)
    {K L : Limits.FormalCoproduct.{w} C} (f : K ⟶ L) :
    covering J f ↔
      ∀ j : L.index, (Hom.fiber f j).toSieve ∈ J (L.obj j) := sorry

namespace covering

/-- Covering morphisms of formal coproducts contain identities and are closed under
composition. -/
@[stacks 01G4 "composition"]
instance isMultiplicative (J : GrothendieckTopology C) :
    (SemiRepresentableFamily.covering J :
      MorphismProperty (Limits.FormalCoproduct.{w} C)).IsMultiplicative := sorry

/-- Covering morphisms of formal coproducts are stable under every existing base change. -/
@[stacks 01G4 "pullback"]
instance isStableUnderBaseChange (J : GrothendieckTopology C) :
    (SemiRepresentableFamily.covering J :
      MorphismProperty (Limits.FormalCoproduct.{w} C)).IsStableUnderBaseChange := sorry

end covering

namespace OverFamily

/-- Definition 25.3.1 (2): the covering property on fixed-target formal coproducts, obtained by
pulling back the ambient covering property along the canonical forgetful functor. -/
@[stacks 01G3 "fixed-target formal-coproduct covering property"]
abbrev covering (J : GrothendieckTopology C) {X : C} :
    MorphismProperty (OverFamily.{v, u, w} X) :=
  (SemiRepresentableFamily.covering J).inverseImage OverFamily.forget

/-- A fixed-target family morphism is covering exactly when its image after forgetting the fixed
target is covering. -/
@[simp] theorem mem_covering_iff (J : GrothendieckTopology C) {X : C}
    {K L : OverFamily.{v, u, w} X} (f : K ⟶ L) :
    OverFamily.covering J f ↔
      SemiRepresentableFamily.covering J (OverFamily.forget.map f) := sorry

namespace covering

/-- Fixed-target covering morphisms are stable under every existing base change. -/
@[stacks 01G4 "fixed-target pullback"]
instance isStableUnderBaseChange (J : GrothendieckTopology C) {X : C} :
    (OverFamily.covering J :
      MorphismProperty (OverFamily.{v, u, w} X)).IsStableUnderBaseChange := sorry

end covering

end OverFamily

end SemiRepresentableFamily

end CategoryTheory
