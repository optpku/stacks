/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.Cech.Conerve.Coprojection
public import ReasLib.AlgebraicTopology.Cech.Nerve.Projection

@[expose] public section

/-!
# Opposite Čech nerve and Čech conerve components

This module owns the objectwise comparison between the Čech conerve of an arrow and the
unopposed Čech nerve of its opposite.  It records the universal-property maps themselves;
their inverse, naturality, and assembled natural isomorphism live in sibling leaves.
-/

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : X ⟶ Y)
variable [(Arrow.mk f).HasCechConerve]

namespace cechConerve

namespace opposite

namespace component

/-- The universal-property relation used to map a Čech-conerve term to the unopposed opposite
Čech-nerve term. -/
@[stacks 019Z "opposite Čech-conerve comparison hom condition"]
theorem homCondition (n : SimplexCategory) (j : Fin (n.len + 1)) :
    f ≫ Quiver.Hom.unop
        (Arrow.cechNerve.π (Arrow.mk f.op) (op n) j) =
      Quiver.Hom.unop
        (Arrow.cechNerve.base (Arrow.mk f.op) (op n)) := sorry

/-- The degreewise map from the Čech conerve of `f` to the unopposed Čech nerve of `f.op`. -/
@[stacks 019Z "opposite Čech-conerve comparison component"]
noncomputable def hom (n : SimplexCategory) :
    ((Arrow.mk f).cechConerve.obj n) ⟶ (Functor.unop ((Arrow.mk f.op).cechNerve)).obj n :=
  Arrow.cechConerve.desc (Arrow.mk f) n
    (Quiver.Hom.unop
      (Arrow.cechNerve.base (Arrow.mk f.op) (op n)))
    (fun j ↦ Quiver.Hom.unop
      (Arrow.cechNerve.π (Arrow.mk f.op) (op n) j))
    (homCondition f n)

/-- The universal-property relation used to map the unopposed opposite Čech nerve back to the
Čech conerve. -/
@[stacks 019Z "inverse opposite Čech-conerve comparison condition"]
theorem invCondition (n : SimplexCategory) (j : Fin (n.len + 1)) :
    (Arrow.cechConerve.ι (Arrow.mk f) n j).op ≫ f.op =
      (Arrow.cechConerve.head (Arrow.mk f) n).op := sorry

/-- The degreewise map from the unopposed Čech nerve of `f.op` back to the Čech conerve of `f`. -/
@[stacks 019Z "inverse opposite Čech-conerve comparison component"]
noncomputable def inv (n : SimplexCategory) :
    (Functor.unop ((Arrow.mk f.op).cechNerve)).obj n ⟶ ((Arrow.mk f).cechConerve.obj n) :=
  Quiver.Hom.unop <|
    Arrow.cechNerve.lift (Arrow.mk f.op) (op n)
      (Arrow.cechConerve.head (Arrow.mk f) n).op
      (fun j ↦ (Arrow.cechConerve.ι (Arrow.mk f) n j).op)
      (invCondition f n)

end component

end opposite

end cechConerve

end CategoryTheory.Arrow
