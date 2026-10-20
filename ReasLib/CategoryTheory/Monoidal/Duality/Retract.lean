/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Retract
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Duality and retracts

The reusable construction is parameterized by an explicit splitting of the mate of the retract
projector.  This keeps the noncanonical splitting visible as data.  Idempotent completeness is
used only by the existence theorem for such a splitting.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y : C}

namespace Retract

/-- A splitting of the left-adjoint mate of the projector associated to a retract. -/
structure LeftDualSplit (r : Retract X Y) [HasLeftDual Y] where
  /-- The object cut out by the dual projector. -/
  object : C
  /-- The selected object is a retract of the chosen left dual of the ambient object. -/
  retract : Retract object (ᘁY : C)
  /-- The complementary composite is the mate of the original retract projector. -/
  projector : retract.r ≫ retract.i = leftAdjointMate (r.r ≫ r.i)

namespace LeftDualSplit

variable [HasLeftDual Y] (r : Retract X Y) (s : LeftDualSplit r)

/-- The coevaluation obtained by restricting the ambient coevaluation along the two retracts. -/
def coevaluation : 𝟙_ C ⟶ s.object ⊗ X :=
  ExactPairing.coevaluation (ᘁY : C) Y ≫ s.retract.r ▷ Y ≫ s.object ◁ r.r

/-- The evaluation obtained by extending to the ambient dual pair along the two retracts. -/
def evaluation : X ⊗ s.object ⟶ 𝟙_ C :=
  r.i ▷ s.object ≫ Y ◁ s.retract.i ≫ ExactPairing.evaluation (ᘁY : C) Y

/-- An explicit splitting of the dual projector determines an exact pairing on the retract. -/
@[implicit_reducible]
def exactPairing : ExactPairing s.object X where
  coevaluation' := s.coevaluation r
  evaluation' := s.evaluation r
  coevaluation_evaluation' := sorry
  evaluation_coevaluation' := sorry

/-- An explicit splitting of the dual projector supplies a chosen left dual of the retract. -/
@[implicit_reducible]
def hasLeftDual : HasLeftDual X where
  leftDual := s.object
  exact := s.exactPairing r

/-- The coevaluation field of the exact pairing induced by a dual-projector splitting. -/
theorem exactPairing_coevaluation' : (s.exactPairing r).coevaluation' = s.coevaluation r := sorry

/-- The evaluation field of the exact pairing induced by a dual-projector splitting. -/
theorem exactPairing_evaluation' : (s.exactPairing r).evaluation' = s.evaluation r := sorry

end LeftDualSplit

/-- In an idempotent-complete monoidal category, the mate of a retract projector admits a
splitting. -/
theorem existsLeftDualSplit [IsIdempotentComplete C] [HasLeftDual Y] (r : Retract X Y) :
    Nonempty (LeftDualSplit r) := sorry

/-- A retract of a left-dualizable object is left dualizable in an idempotent-complete monoidal
category.  The result is stated as existence because the idempotent splitting is noncanonical. -/
@[stacks 0FFU]
theorem existsHasLeftDual [IsIdempotentComplete C] [HasLeftDual Y] (r : Retract X Y) :
    Nonempty (HasLeftDual X) := sorry

end Retract

end CategoryTheory
