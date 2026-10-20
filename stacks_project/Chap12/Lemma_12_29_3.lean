module

public import ReasLib.CategoryTheory.Adjunction.Abelian
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 12.29.3 compatibility facade

The reusable enough-injectives transfer criterion is owned by
`ReasLib.CategoryTheory.Adjunction.Abelian`. This module retains the historical Chapter 12
import path.
-/

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {L : A ⥤ B} {R : B ⥤ A} [R.Additive]
variable [R.PreservesMonomorphisms] [EnoughInjectives A]
variable (adj : R ⊣ L) (h_zero : R.kernel ≤ IsZero)

/- Lemma 12.29.3 is the shared enough-injectives transfer criterion. -/
@[stacks 0160]
#check (Adjunction.RightAdjoint.enoughInjectives_of_leftPreservesMonomorphisms adj h_zero :
  EnoughInjectives B)

end CategoryTheory
