/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.Cech.Conerve.Opposite.Computations
public import ReasLib.CategoryTheory.Arrow.Opposite

@[expose] public section

/-!
# Natural opposite Čech comparison

This module assembles the componentwise comparison of a Čech conerve with the unopposed Čech
nerve of the opposite arrow into its reusable natural isomorphism.
-/

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.Arrow.cechConerve.opposite

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (f : X ⟶ Y)
variable [(Arrow.mk f).HasCechConerve]

namespace component

/-- The degreewise inverse comparison between the Čech conerve of `f` and the unopposed
Čech nerve of `f.op`. -/
@[stacks 019Z "opposite Čech-conerve component isomorphism"]
noncomputable def iso (n : SimplexCategory) :
    ((Arrow.mk f).cechConerve.obj n) ≅ (Functor.unop ((Arrow.mk f.op).cechNerve)).obj n :=
  { hom := hom f n
    inv := inv f n
    hom_inv_id := hom_inv_id f n
    inv_hom_id := inv_hom_id f n }

end component

/-- The Čech conerve of `f` is naturally isomorphic to the unopposed Čech nerve of `f.op`. -/
@[stacks 019Z "opposite Čech-conerve natural isomorphism"]
noncomputable def iso :
    (Arrow.mk f).cechConerve ≅ Functor.unop ((Arrow.mk f.op).cechNerve) :=
  NatIso.ofComponents
    (fun n ↦ component.iso f n)
    (fun {_ _} α ↦ component.hom_naturality (f := f) α)

namespace iso

/-- The hom component of the natural Čech comparison is the universal map out of the
corresponding Čech conerve term. -/
@[simp, stacks 019Z "opposite Cech-conerve hom component"]
theorem hom_app (n : SimplexCategory) :
    (iso f).hom.app n = component.hom f n := sorry

/-- The inv component of the natural Čech comparison is the universal map into the
corresponding Čech conerve term. -/
@[simp, stacks 019Z "opposite Cech-conerve inverse component"]
theorem inv_app (n : SimplexCategory) :
    (iso f).inv.app n = component.inv f n := sorry

/-- Naturality of the hom side of the natural Čech-conerve/opposite-Čech-nerve comparison. -/
@[stacks 019Z "opposite Cech-conerve component naturality"]
theorem hom_naturality {n m : SimplexCategory} (α : n ⟶ m) :
    ((Arrow.mk f).cechConerve).map α ≫ (iso f).hom.app m =
      (iso f).hom.app n ≫
        (Functor.unop ((Arrow.mk f.op).cechNerve)).map α := sorry

/-- Conjugating the unopposed opposite Čech-nerve map of a commutative square by the endpoint
comparisons recovers the corresponding Čech-conerve map. -/
@[stacks 019Z "opposite Čech-conerve comparison naturality in arrows"]
theorem map {X' Y' : C} {g : X' ⟶ Y'}
    [(Arrow.mk g).HasCechConerve] (F : Arrow.mk f ⟶ Arrow.mk g) :
    (iso f).hom ≫
        NatTrans.unop
          (Arrow.mapCechNerve ((Arrow.opFunctor C).map F.op)) ≫
          (iso g).inv =
      Arrow.mapCechConerve F := sorry

/-- Conjugating the identity of the unopposed opposite Čech nerve by the comparison gives the
identity of the Čech conerve. -/
@[stacks 019Z "opposite Cech-conerve comparison identity"]
theorem id :
    (iso f).hom ≫ NatTrans.unop (𝟙 ((Arrow.mk f.op).cechNerve)) ≫ (iso f).inv =
      𝟙 ((Arrow.mk f).cechConerve) := sorry

end iso

end CategoryTheory.Arrow.cechConerve.opposite
