/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Pullback.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]
variable (p : E ⥤ C) {x y z w : E} (phi : x ⟶ y) (psi : z ⟶ y)
variable {R : C} {f : R ⟶ p.obj x} {g : R ⟶ p.obj z}
variable (hbase : IsPullback f g (p.map phi) (p.map psi)) (a : w ⟶ z)
variable [p.IsStronglyCartesian (p.map phi) phi] [p.IsStronglyCartesian g a]

/- Lemma 4.33.4: a pullback square in the base lifts to a pullback square in the total category
when the relevant legs are strongly cartesian. The canonical first leg is supplied by the
strongly-cartesian map API, so callers do not have to provide a separate lift and compatibility
proof. -/
@[stacks 06N4]
#check (Functor.IsStronglyCartesian.isPullback_of_base_map p phi psi hbase a :
  IsPullback
    (Functor.IsStronglyCartesian.map p (p.map phi) phi hbase.w.symm (a ≫ psi))
    a phi psi)

end CategoryTheory
