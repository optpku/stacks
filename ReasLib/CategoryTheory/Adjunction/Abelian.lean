/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import ReasLib.CategoryTheory.Functor.Exactness.Faithful
import Mathlib.Tactic.CrossRefAttribute

/-!
# Abelian consequences of adjunctions

This leaf isolates exactness, injectivity, and enough-injectives consequences of an
adjunction between abelian categories.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Adjunction

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {L : A ⥤ B} {R : B ⥤ A}

namespace RightAdjoint

/-- Explicit-adjunction form of the exactness criterion for a right adjoint which preserves
epimorphisms. -/
theorem exact_of_preservesEpimorphisms
    (adj : L ⊣ R) (hR : R.PreservesEpimorphisms) :
    exactFunctor B A R := sorry

end RightAdjoint

end

end Adjunction

namespace Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- Explicit-evidence bridge for exactness of a right adjoint which preserves epimorphisms.
This form lets callers pass a locally available witness without registering a temporary
instance. -/
theorem exact_of_preservesEpimorphisms_of
    (R : B ⥤ A) [R.IsRightAdjoint]
    (hR : R.PreservesEpimorphisms) :
    exactFunctor B A R := sorry

/-- A right adjoint between abelian categories is exact when it preserves epimorphisms. -/
@[stacks 04DB "right-adjoint criterion"]
theorem exact_of_preservesEpimorphisms
    (R : B ⥤ A) [R.IsRightAdjoint] [R.PreservesEpimorphisms] :
    exactFunctor B A R := sorry

end Functor

namespace Adjunction

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {u : A ⥤ B} {v : B ⥤ A} [v.Additive]

namespace LeftAdjoint

/-- An additive left adjoint between abelian categories preserves monomorphisms exactly when it
is exact. -/
@[stacks 015Z "(1)"]
theorem preservesMonomorphisms_iff_exact
    (adj : v ⊣ u) :
    v.PreservesMonomorphisms ↔ exactFunctor _ _ v := sorry

end LeftAdjoint

end

section

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {u : A ⥤ B} {v : B ⥤ A}

namespace RightAdjoint

/-- A right adjoint preserves injective objects when its left adjoint is exact. -/
@[stacks 015Z "(2)"]
theorem preservesInjectiveObjects_of_leftExact
    (adj : v ⊣ u) (h_exact : exactFunctor _ _ v) :
    u.PreservesInjectiveObjects := sorry

end RightAdjoint

end

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {u : A ⥤ B} {v : B ⥤ A} [v.Additive]

/-- An additive left adjoint that preserves monomorphisms reflects zero objects exactly when it
is faithful. -/
@[stacks 03B9 "(1)"]
theorem kernel_le_isZero_iff_faithful
    (adj : v ⊣ u) [v.PreservesMonomorphisms] :
    v.kernel ≤ IsZero ↔ v.Faithful := sorry

namespace RightAdjoint

/-- Enough injectives transfer across a right adjoint when its left adjoint preserves
monomorphisms and detects zero objects. -/
@[stacks 0160]
theorem enoughInjectives_of_leftPreservesMonomorphisms
    (adj : v ⊣ u) [v.PreservesMonomorphisms] [EnoughInjectives A]
    (h_zero : v.kernel ≤ IsZero) :
    EnoughInjectives B := sorry

end RightAdjoint

end

end Adjunction

end CategoryTheory
