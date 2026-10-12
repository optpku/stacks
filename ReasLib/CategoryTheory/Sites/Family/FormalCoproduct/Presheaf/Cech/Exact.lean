/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import ReasLib.AlgebraicTopology.CosimplicialObject.DoldKan.AlternatingCofaceMapComplex
public import ReasLib.CategoryTheory.Functor.Exactness.Composition
public import ReasLib.CategoryTheory.Functor.Exactness.Pointwise
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exactness of formal-coproduct Cech functors

The formal-coproduct Cech construction is factored into its evaluation and
alternating-coface stages.  The one-sided declarations keep the product
exactness hypothesis on the colimit side only.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u v' u'

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]
variable {A : Type u'} [Category.{v'} A]

variable (E : SimplicialObject (FormalCoproduct.{w} C))

namespace cosimplicialObjectFunctor

/-- Evaluation on a simplicial formal coproduct is left exact whenever the relevant products
exist. -/
@[stacks 03AP "left exact formal-coproduct Cech cosimplicial functor"]
theorem leftExact [HasProducts.{w} A] :
    leftExactFunctor (Cᵒᵖ ⥤ A) (CosimplicialObject A)
      (FormalCoproduct.cosimplicialObjectFunctor E) := sorry

/-- Evaluation on a simplicial formal coproduct is right exact when the relevant products are
exact. -/
@[stacks 03AP "right exact formal-coproduct Cech cosimplicial functor"]
theorem rightExact [Abelian A] [HasProducts.{w} A] [AB4StarOfSize.{w} A] :
    rightExactFunctor (Cᵒᵖ ⥤ A) (CosimplicialObject A)
      (FormalCoproduct.cosimplicialObjectFunctor E) := sorry

/-- Evaluation on a simplicial formal coproduct is exact when the relevant products are exact. -/
@[stacks 03AP "exact formal-coproduct Cech cosimplicial functor"]
theorem exact [Abelian A] [HasProducts.{w} A] [AB4StarOfSize.{w} A] :
    exactFunctor (Cᵒᵖ ⥤ A) (CosimplicialObject A)
      (FormalCoproduct.cosimplicialObjectFunctor E) := sorry

end cosimplicialObjectFunctor

namespace cochainComplexFunctor

/-- The formal-coproduct Cech cochain-complex functor is left exact under product existence. -/
@[stacks 03AP "left exact formal-coproduct Cech complex functor"]
theorem leftExact [Preadditive A] [HasFiniteLimits A] [HasProducts.{w} A] :
    leftExactFunctor (Cᵒᵖ ⥤ A) (CochainComplex A ℕ)
      (FormalCoproduct.cochainComplexFunctor E) := sorry

/-- The formal-coproduct Cech cochain-complex functor is right exact when products are exact. -/
@[stacks 03AP "right exact formal-coproduct Cech complex functor"]
theorem rightExact [Abelian A] [HasProducts.{w} A] [AB4StarOfSize.{w} A] :
    rightExactFunctor (Cᵒᵖ ⥤ A) (CochainComplex A ℕ)
      (FormalCoproduct.cochainComplexFunctor E) := sorry

/-- The formal-coproduct Cech cochain-complex functor is exact when products are exact. -/
@[stacks 03AP "exact formal-coproduct Cech complex functor"]
theorem exact [Abelian A] [HasProducts.{w} A] [AB4StarOfSize.{w} A] :
    exactFunctor (Cᵒᵖ ⥤ A) (CochainComplex A ℕ)
      (FormalCoproduct.cochainComplexFunctor E) := sorry

end cochainComplexFunctor

end CategoryTheory.Limits.FormalCoproduct
