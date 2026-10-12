/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.Cech.Conerve.Opposite.Basic

@[expose] public section

/-!
# Computations for opposite Čech comparisons

This module records the universal-leg formulas, inverse identities, and simplex-operator
naturality of the componentwise comparison in `Cech.Conerve.Opposite.Basic`.
-/

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.Arrow.cechConerve.opposite.component

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : X ⟶ Y)
variable [(Arrow.mk f).HasCechConerve]

/-- The forward comparison sends each Čech-conerve branch coprojection to the corresponding
opposite Čech-nerve projection. -/
@[reassoc (attr := simp), stacks 019Z "opposite Čech-conerve branch comparison"]
theorem hom_ι (n : SimplexCategory) (j : Fin (n.len + 1)) :
    Arrow.cechConerve.ι (Arrow.mk f) n j ≫
        hom f n =
      Quiver.Hom.unop
        (Arrow.cechNerve.π (Arrow.mk f.op) (op n) j) := sorry

/-- The forward comparison sends the Čech-conerve head coprojection to the opposite
Čech-nerve base map. -/
@[reassoc (attr := simp), stacks 019Z "opposite Čech-conerve head comparison"]
theorem hom_head (n : SimplexCategory) :
    Arrow.cechConerve.head (Arrow.mk f) n ≫
        hom f n =
      Quiver.Hom.unop
        (Arrow.cechNerve.base (Arrow.mk f.op) (op n)) := sorry

/-- Precomposing the inverse comparison with the opposite Čech-nerve base map recovers the
Čech-conerve head coprojection. -/
@[reassoc (attr := simp), stacks 019Z "opposite Čech-conerve inverse head comparison"]
theorem inv_head (n : SimplexCategory) :
    Quiver.Hom.unop
        (Arrow.cechNerve.base (Arrow.mk f.op) (op n)) ≫
        inv f n =
      Arrow.cechConerve.head (Arrow.mk f) n := sorry

/-- Precomposing the inverse comparison with an opposite Čech-nerve projection recovers the
corresponding Čech-conerve branch coprojection. -/
@[reassoc (attr := simp), stacks 019Z "opposite Čech-conerve inverse branch comparison"]
theorem inv_ι (n : SimplexCategory) (j : Fin (n.len + 1)) :
    Quiver.Hom.unop
        (Arrow.cechNerve.π (Arrow.mk f.op) (op n) j) ≫
        inv f n =
      Arrow.cechConerve.ι (Arrow.mk f) n j := sorry

/-- The forward and inverse component maps compose to the identity on the Čech-conerve term. -/
@[stacks 019Z "opposite Čech-conerve component hom-inverse identity"]
theorem hom_inv_id (n : SimplexCategory) :
    hom f n ≫ inv f n =
      𝟙 ((Arrow.mk f).cechConerve.obj n) := sorry

/-- The inverse and forward component maps compose to the identity on the unopposed opposite
Čech-nerve term. -/
@[stacks 019Z "opposite Čech-conerve component inverse-hom identity"]
theorem inv_hom_id (n : SimplexCategory) :
    inv f n ≫ hom f n =
      𝟙 ((Functor.unop ((Arrow.mk f.op).cechNerve)).obj n) := sorry

/-- The forward component maps commute with every simplex operator. -/
@[stacks 019Z "opposite Čech-conerve component naturality"]
theorem hom_naturality {n m : SimplexCategory} (α : n ⟶ m) :
    ((Arrow.mk f).cechConerve).map α ≫ hom f m =
      hom f n ≫
        (Functor.unop ((Arrow.mk f.op).cechNerve)).map α := sorry

end CategoryTheory.Arrow.cechConerve.opposite.component
