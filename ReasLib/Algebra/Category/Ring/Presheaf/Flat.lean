/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat restriction maps of a commutative-ring presheaf

Flatness of restriction maps depends only on the coefficient presheaf.  This file owns that
condition before any module-presheaf, sheaf, or topology-specific specialization is introduced.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.Presheaf.Restriction

variable {C : Type u} [Category.{v} C]

/-- Lemma 18.24.4 (0GZP): a commutative-ring presheaf has flat restriction maps when every
morphism it assigns is in the canonical morphism property `CommRingCat.flat`. -/
@[stacks 0GZP "flat restriction maps"]
class Flat (O : Cᵒᵖ ⥤ CommRingCat.{w}) : Prop where
  /-- Every restriction morphism of the coefficient presheaf is flat. -/
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : CommRingCat.flat (O.map f)

namespace Flat

variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The ring-homomorphism form of flatness of a restriction map. -/
theorem map_ringHom [Flat O] {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    RingHom.Flat ((O.map f).hom) := sorry

/-- Construct flat restriction maps from the corresponding pointwise ring-homomorphism
condition. -/
theorem ofRingHom
    (h : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y), RingHom.Flat ((O.map f).hom)) : Flat O := sorry

end Flat

end CategoryTheory.Presheaf.Restriction
