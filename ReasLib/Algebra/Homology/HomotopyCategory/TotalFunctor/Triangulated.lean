/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import ReasLib.Algebra.Homology.HomologicalComplex.Biproduct
public import ReasLib.Algebra.Homology.HomotopyCategory.TotalFunctor

/-!
# Exactness of fixed-factor bifunctor totalization

@stack 0G6E
@stack 064J

The fixed-factor totalization functors on homotopy categories preserve distinguished triangles.
This file is separate from the descent and computation API so that users who only need the
underlying functors do not acquire the triangulated-category assumptions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory
open HomologicalComplex

noncomputable section

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor.Homotopy.BifunctorTotal

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Category.{v₃} 𝒞]
  [Preadditive 𝒜] [Preadditive ℬ] [Preadditive 𝒞]

variable (tensor : 𝒜 ⥤ ℬ ⥤ 𝒞)
  [tensor.Additive] [∀ X : 𝒜, (tensor.obj X).Additive]
  [∀ (X : CochainComplex 𝒜 ℤ) (Y : CochainComplex ℬ ℤ),
    CochainComplex.HasMapBifunctor X Y tensor]

/-- Fixed-left bifunctor totalization is an exact functor on homotopy categories. -/
@[stacks 0G6E, stacks 064J "exactness of left fixed-factor bifunctor totalization"]
noncomputable instance leftFixedIsTriangulated
    [HasZeroObject ℬ] [HasZeroObject 𝒞]
    [HasBinaryBiproducts ℬ] [HasBinaryBiproducts 𝒞]
    (X : CochainComplex 𝒜 ℤ) :
    (leftFixed tensor X).IsTriangulated := sorry

/-- Fixed-right bifunctor totalization is an exact functor on homotopy categories. -/
@[stacks 0G6E, stacks 064J "exactness of right fixed-factor bifunctor totalization"]
noncomputable instance rightFixedIsTriangulated
    [HasZeroObject 𝒜] [HasZeroObject 𝒞]
    [HasBinaryBiproducts 𝒜] [HasBinaryBiproducts 𝒞]
    (Y : CochainComplex ℬ ℤ) :
    (rightFixed tensor Y).IsTriangulated := sorry



end CategoryTheory.Functor.Homotopy.BifunctorTotal
