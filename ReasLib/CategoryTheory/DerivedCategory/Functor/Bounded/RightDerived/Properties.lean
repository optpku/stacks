/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Basic Properties of Bounded-Below Right Derived Functors

This leaf contains the degree bounds and degree-zero exactness consequences of
a chosen bounded-below right derived functor.  The construction and comparison
data remain in `RightDerived.Comparison`; this module is Proposition-only.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]
  (RF : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ)
  (α : F.toBoundedBelowDerived ⟶ DerivedCategory.Plus.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso 𝒜)]

namespace RightDerived.degree

include F α

/-- Stacks 05TD (1): a bounded-below right derived functor has no negative
cohomological degrees on degree-zero objects. -/
@[stacks 05TD]
theorem isZero_of_neg
    (i : ℤ) (hi : i < 0) :
    IsZero (Functor.RightDerived.degree RF i) := sorry

end RightDerived.degree

include F α

/-- Stacks 05TD (2): degree zero of a bounded-below right derived functor is
left exact. -/
@[stacks 05TD]
theorem RightDerived.zero.preservesFiniteLimits :
    PreservesFiniteLimits (Functor.RightDerived.degree RF 0) := sorry

/-- Stacks 05TD (3): the degree-zero comparison is invertible exactly when
the original additive functor is left exact. -/
@[stacks 05TD]
theorem RightDerived.zero.isIso_iff_preservesFiniteLimits :
    IsIso (Functor.RightDerived.zero F RF α) ↔ PreservesFiniteLimits F := sorry

omit α

namespace RightDerived.Bounded

variable [F.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso 𝒜)]

/-- The canonical bounded-below right-derived functor has no negative
cohomological degrees. -/
@[stacks 05TD]
theorem degree.isZero_of_neg (i : ℤ) (hi : i < 0) :
    IsZero (degree F i) := sorry

namespace degree

variable [HasInjectiveResolutions 𝒜] [PreservesFiniteLimits F]

/-- In nonnegative degree, the canonical bounded-below right-derived functor agrees with the
ordinary injective-resolution right-derived functor. -/
@[stacks 015A "bounded and ordinary right-derived degree comparison"]
theorem isIsomorphic_rightDerived (n : ℕ) :
    IsIsomorphic (degree F (Int.ofNat n)) (F.rightDerived n) := sorry

end degree

/-- Degree zero of the canonical bounded-below right-derived functor is left
exact. -/
@[stacks 05TD]
theorem zero.preservesFiniteLimits :
    PreservesFiniteLimits (degree F 0) := sorry

/-- Degree zero of the canonical bounded-below right-derived functor is left exact as a
typeclass instance. -/
@[stacks 05TD "canonical bounded right-derived degree-zero instance"]
instance degree.preservesFiniteLimits : PreservesFiniteLimits (degree F 0) := sorry

/-- The canonical degree-zero comparison is invertible exactly when the
underived functor is left exact. -/
@[stacks 05TD]
theorem zero.isIso_iff_preservesFiniteLimits :
    IsIso (zero F) ↔ PreservesFiniteLimits F := sorry

/-- For a left exact functor, the canonical bounded-below degree-zero comparison is an
isomorphism available to typeclass search. -/
@[stacks 05TD "canonical bounded right-derived comparison instance"]
instance zero.isIso [PreservesFiniteLimits F] : IsIso (zero F) := sorry

end RightDerived.Bounded

end Functor


end CategoryTheory
