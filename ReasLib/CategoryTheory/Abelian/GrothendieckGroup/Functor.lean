/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckGroup
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of Abelian Grothendieck Groups

An exact functor between abelian categories preserves the short-exact relations and therefore
induces an additive homomorphism on Grothendieck groups.
-/

@[expose] public section

open CategoryTheory

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.AbelianK0

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- The object map of an exact functor kills the defining Grothendieck relations. -/
theorem relations_le_map_ker (F : A ⥤ₑ B) :
    relations A ≤
      (FreeAbelianGroup.lift fun X ↦ K₀[F.obj.obj X]).ker := sorry

/-- The additive homomorphism on Grothendieck groups induced by an exact functor. -/
@[stacks 02MV]
def map (F : A ⥤ₑ B) : AbelianK0 A →+ AbelianK0 B :=
  lift (fun X ↦ K₀[F.obj.obj X]) (relations_le_map_ker F)

/-- The induced homomorphism sends an object class to the class of its image. -/
@[simp]
theorem map_of (F : A ⥤ₑ B) (X : A) :
    map F K₀[X] = K₀[F.obj.obj X] := sorry

end CategoryTheory.AbelianK0
