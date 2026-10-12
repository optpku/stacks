/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced.Computations.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LocallyInduced.Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lift computations for locally induced pseudopullback cones

This leaf records the round-trip computation for the explicit ambient-to-locally-induced cone
lift. The field-level readouts remain in `LocallyInduced.Lift`; this theorem is the compact
downstream rewriting form.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u w' v' u'

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {C : Type u'} [Bicategory.{w', v'} C]
variable (P : ObjectProperty C)
variable (Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1))
variable [Q.IsMultiplicative]
variable {X Y Z : Bicategory.LocallyInducedBicategory C
  (fun X : P.FullSubbicategory ↦ X.1) Q}
variable {f : X ⟶ Z} {g : Y ⟶ Z}

/-- Forgetting a locally induced lift of an ambient pseudo-pullback cone recovers that cone. -/
@[simp]
theorem inLocallyInduced.forget
    (S : PseudoPullbackCone f.obj g.obj) (hS : P S.pt)
    (hfst : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) X S.fst)
    (hsnd : Q (ObjectProperty.FullSubbicategory.mk P S.pt hS) Y S.snd) :
    (inLocallyInduced P Q S hS hfst hsnd).forgetLocallyInduced = S := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
