module

public import ReasLib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Abelian.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 12.29.6 compatibility facade

The reusable right-adjoint criterion from an epimorphically covering object
property is owned by `ReasLib.CategoryTheory.Adjunction.PartialAdjoint`. This
module retains the historical Chapter 12 import path.
-/

open CategoryTheory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (u : A ⥤ B) (P : ObjectProperty B) [P.HasEpiCover]
variable (hdefined : P ≤ u.leftAdjointObjIsDefined)

/- Lemma 12.29.6: a functor between abelian categories has a left adjoint when
an epimorphically covering object property corepresents Hom(P, u(-)). -/
@[stacks 0793]
#check (Functor.isRightAdjoint_of_hasEpiCover u P hdefined : u.IsRightAdjoint)

end CategoryTheory
