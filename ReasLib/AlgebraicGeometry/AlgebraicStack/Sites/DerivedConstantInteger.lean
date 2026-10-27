/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived.ConstantSheaf
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedLowerShriek
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived lower shriek of the constant integer sheaf on algebraic stacks

The canonical comparisons along the lisse-étale and flat-fppf inclusions
identify derived lower shriek of the constant integer sheaf with the constant
integer sheaf in the unbounded derived category.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/-- The canonical comparison from the constant integer sheaf on the lisse-étale
site to the inverse image of the constant integer sheaf on the associated étale
site. -/
def lisseEtaleInverseImage_constantInteger_hom :
    constantIntegerSheaf (lisseEtaleTopology X) ⟶
      ((lisseEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
          (lisseEtaleTopology X) X.etaleTopology).obj
        (constantIntegerSheaf X.etaleTopology) :=
  (lisseEtaleInclusion X).constantSheafRestrictionHom
    (lisseEtaleTopology X) X.etaleTopology AddCommGrpCat.{z}
    (AddCommGrpCat.of (ULift.{z} ℤ))

/-- The canonical comparison from the constant integer sheaf on the flat-fppf
site to the inverse image of the constant integer sheaf on the inherited fppf
site. -/
def flatFppfInverseImage_constantInteger_hom :
    constantIntegerSheaf (flatFppfTopology X) ⟶
      ((flatFppfInclusion X).sheafPushforwardContinuous AddCommGrpCat.{z}
          (flatFppfTopology X) (inheritedFppfTopology X)).obj
        (constantIntegerSheaf (inheritedFppfTopology X)) :=
  (flatFppfInclusion X).constantSheafRestrictionHom
    (flatFppfTopology X) (inheritedFppfTopology X) AddCommGrpCat.{z}
    (AddCommGrpCat.of (ULift.{z} ℤ))

/-- The canonical derived comparison `Lg_! ℤ ⟶ ℤ` along the lisse-étale
inclusion of an algebraic stack. -/
def lisseEtaleAbelianLowerShriekDerived_constantInteger :
    (lisseEtaleAbelianLowerShriekDerived X).obj
        ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (constantIntegerSheaf (lisseEtaleTopology X))) ⟶
      (DerivedCategory.singleFunctor _ (0 : ℤ)).obj
        (constantIntegerSheaf X.etaleTopology) :=
  Functor.AbelianLowerShriek.derived.constantSheafComparison
    (lisseEtaleTopology X) X.etaleTopology (lisseEtaleInclusion X)
    (AddCommGrpCat.of (ULift.{z} ℤ))

/-- The canonical derived comparison `Lg_! ℤ ⟶ ℤ` along the flat-fppf
inclusion of an algebraic stack. -/
def flatFppfAbelianLowerShriekDerived_constantInteger :
    (flatFppfAbelianLowerShriekDerived X).obj
        ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (constantIntegerSheaf (flatFppfTopology X))) ⟶
      (DerivedCategory.singleFunctor _ (0 : ℤ)).obj
        (constantIntegerSheaf (inheritedFppfTopology X)) :=
  Functor.AbelianLowerShriek.derived.constantSheafComparison
    (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X)
    (AddCommGrpCat.of (ULift.{z} ℤ))

/-- The canonical lisse-étale derived lower-shriek comparison on the constant
integer sheaf of an algebraic stack is an isomorphism. -/
@[stacks 0H0Z]
instance lisseEtaleAbelianLowerShriekDerived_constantInteger.instIsIso :
    IsIso (lisseEtaleAbelianLowerShriekDerived_constantInteger X) := sorry

/-- The canonical flat-fppf derived lower-shriek comparison on the constant
integer sheaf of an algebraic stack is an isomorphism. -/
@[stacks 0H0Z]
instance flatFppfAbelianLowerShriekDerived_constantInteger.instIsIso :
    IsIso (flatFppfAbelianLowerShriekDerived_constantInteger X) := sorry

end AlgebraicGeometry.AlgebraicStack
