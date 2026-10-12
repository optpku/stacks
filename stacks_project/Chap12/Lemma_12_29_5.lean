/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Adjunction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 12.29.5 compatibility facade

The reusable functorial-injective-embedding transfer is owned by
`ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Adjunction`. This module
retains the historical Chapter 12 import path.
-/

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {L : A ⥤ B} {R : B ⥤ A}
variable [HasFunctorialInjectives A]
variable [Abelian A] [Abelian B] [R.Additive] [R.PreservesMonomorphisms]
variable (adj : R ⊣ L)
variable (h_zero : ∀ X : B, IsZero (R.obj X) → IsZero X)

/- Lemma 12.29.5 is the shared functorial injective-embedding transfer. -/
@[stacks 0161]
#check (HasFunctorialInjectives.of_rightAdjoint adj h_zero :
  HasFunctorialInjectives B)

end CategoryTheory
