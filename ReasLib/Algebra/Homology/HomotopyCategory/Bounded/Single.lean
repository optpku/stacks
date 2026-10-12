/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import Mathlib.CategoryTheory.Shift.SingleFunctors

@[expose] public section

/-!
# Single Complexes in Bounded Homotopy Categories

This leaf lifts the canonical family of single-complex functors to the bounded-above and bounded
homotopy categories and exposes their comparisons with the ambient homotopy category.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v u

namespace CategoryTheory

namespace HomotopyCategory.Minus

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]

/-- A degree-`n` single complex is bounded above after passing to the homotopy category. -/
theorem single_obj_mem (n : ℤ) (A : 𝒜) :
    HomotopyCategory.minus 𝒜 ((HomotopyCategory.singleFunctor 𝒜 n).obj A) := sorry

/-- The shift-compatible family of single-complex functors with values in `K⁻(𝒜)`. -/
@[stacks 015A]
noncomputable def singleFunctors : SingleFunctors 𝒜 (HomotopyCategory.Minus 𝒜) ℤ :=
  SingleFunctors.lift (HomotopyCategory.singleFunctors 𝒜) (ι 𝒜)
    (fun n ↦ (HomotopyCategory.minus 𝒜).lift
      (HomotopyCategory.singleFunctor 𝒜 n)
      (single_obj_mem 𝒜 n))
    (fun _ ↦ Iso.refl _)

/-- The degree-`n` single-complex functor with values in `K⁻(𝒜)`. -/
@[stacks 015A]
noncomputable abbrev singleFunctor (n : ℤ) : 𝒜 ⥤ HomotopyCategory.Minus 𝒜 :=
  (singleFunctors 𝒜).functor n

/-- Forgetting the bounded-above structure on `singleFunctor` recovers the ambient single
complex functor. -/
@[stacks 015A]
noncomputable def singleFunctorCompιIso (n : ℤ) :
    singleFunctor 𝒜 n ⋙ (HomotopyCategory.minus 𝒜).ι ≅
      HomotopyCategory.singleFunctor 𝒜 n :=
  Iso.refl _

/-- The bounded-above single-complex functor is additive. -/
instance singleFunctor.additive (n : ℤ) : (singleFunctor 𝒜 n).Additive := sorry

end HomotopyCategory.Minus

namespace HomotopyCategory.Bounded

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]

/-- A degree-`n` single complex is bounded after passing to the homotopy category. -/
theorem single_obj_mem (n : ℤ) (A : 𝒜) :
    HomotopyCategory.bounded 𝒜 ((HomotopyCategory.singleFunctor 𝒜 n).obj A) := sorry

/-- The shift-compatible family of single-complex functors with values in `Kᵇ(𝒜)`. -/
@[stacks 0FCP]
noncomputable def singleFunctors : SingleFunctors 𝒜 (HomotopyCategory.Bounded 𝒜) ℤ :=
  SingleFunctors.lift (HomotopyCategory.singleFunctors 𝒜) (ι 𝒜)
    (fun n ↦ (HomotopyCategory.bounded 𝒜).lift
      (HomotopyCategory.singleFunctor 𝒜 n)
      (single_obj_mem 𝒜 n))
    (fun _ ↦ Iso.refl _)

/-- The degree-`n` single-complex functor with values in `Kᵇ(𝒜)`. -/
@[stacks 0FCP]
noncomputable abbrev singleFunctor (n : ℤ) : 𝒜 ⥤ HomotopyCategory.Bounded 𝒜 :=
  (singleFunctors 𝒜).functor n

/-- Forgetting the bounded structure on `singleFunctor` recovers the ambient single-complex
functor. -/
@[stacks 0FCP]
noncomputable def singleFunctorCompιIso (n : ℤ) :
    singleFunctor 𝒜 n ⋙ (HomotopyCategory.bounded 𝒜).ι ≅
      HomotopyCategory.singleFunctor 𝒜 n :=
  Iso.refl _

/-- The bounded single-complex functor is additive. -/
instance singleFunctor.additive (n : ℤ) : (singleFunctor 𝒜 n).Additive := sorry

end HomotopyCategory.Bounded

end CategoryTheory


