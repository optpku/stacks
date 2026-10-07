module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive.Computation
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Induced Functors from Homotopy to Derived Categories

For an additive functor `F : 𝒜 ⥤ ℬ`, `Functor.Homotopy.toDerived F` is the
canonical functor `K(𝒜) ⥤ D(ℬ)`. This module adds its three standard bounded
source restrictions:

* The bounded-below variant `K⁺(𝒜) ⥤ D(ℬ)` (restricting to plus subcategory).
* The bounded-above variant `K⁻(𝒜) ⥤ D(ℬ)` (restricting to minus subcategory).
* The bounded variant `Kᵇ(𝒜) ⥤ D(ℬ)`.

These are the starting points for bounded derived functors. There is no second
unbounded owner in this file.

## Main definitions

* `Functor.Homotopy.Plus.toDerived` — the restriction `K⁺(𝒜) ⥤ D(ℬ)`.
* `Functor.Homotopy.Minus.toDerived` — the restriction `K⁻(𝒜) ⥤ D(ℬ)`.
* `Functor.Homotopy.Bounded.toDerived` — the restriction `Kᵇ(𝒜) ⥤ D(ℬ)`.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

namespace Homotopy

variable {𝒜 : Type u₁} {ℬ : Type u₂} [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]

section

variable [HasDerivedCategory ℬ]

/-- The induced functor restricted to bounded-below objects: `K⁺(𝒜) ⥤ D(ℬ)`. -/
@[stacks 05T4]
def Plus.toDerived (F : 𝒜 ⥤ ℬ) [F.Additive] : K⁺(𝒜) ⥤ D(ℬ) :=
  (HomotopyCategory.plus 𝒜).ι ⋙ Homotopy.toDerived F

/-- The induced functor restricted to bounded-above objects: `K⁻(𝒜) ⥤ D(ℬ)`. -/
@[stacks 05T4]
def Minus.toDerived (F : 𝒜 ⥤ ℬ) [F.Additive] : K⁻(𝒜) ⥤ D(ℬ) :=
  (HomotopyCategory.minus 𝒜).ι ⋙ Homotopy.toDerived F

/-- The induced functor restricted to bounded objects: `Kᵇ(𝒜) ⥤ D(ℬ)`. -/
@[stacks 05T4]
def Bounded.toDerived (F : 𝒜 ⥤ ℬ) [F.Additive] : Kᵇ(𝒜) ⥤ D(ℬ) :=
  (HomotopyCategory.bounded 𝒜).ι ⋙ Homotopy.toDerived F

/-- Definitional unfolding of the bounded-below restriction. -/
theorem Plus.toDerived_eq (F : 𝒜 ⥤ ℬ) [F.Additive] :
    Plus.toDerived F = (HomotopyCategory.plus 𝒜).ι ⋙ Homotopy.toDerived F :=
  rfl

/-- Definitional unfolding of the bounded-above restriction. -/
theorem Minus.toDerived_eq (F : 𝒜 ⥤ ℬ) [F.Additive] :
    Minus.toDerived F = (HomotopyCategory.minus 𝒜).ι ⋙ Homotopy.toDerived F :=
  rfl

/-- Definitional unfolding of the bounded restriction. -/
theorem Bounded.toDerived_eq (F : 𝒜 ⥤ ℬ) [F.Additive] :
    Bounded.toDerived F = (HomotopyCategory.bounded 𝒜).ι ⋙ Homotopy.toDerived F :=
  rfl

end


end Homotopy

end Functor

end CategoryTheory
