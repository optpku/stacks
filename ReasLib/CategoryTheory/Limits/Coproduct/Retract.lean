module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coproduct summands as retracts

In a category with zero morphisms, every object in an indexed coproduct is canonically a
retract of that coproduct.  Mathlib provides the inclusion `Sigma.ι`, the projection `Sigma.π`,
and their computation rule; this leaf packages them as a `Retract` for direct use by
retract-stable object properties.
-/

@[expose] public section

open CategoryTheory

universe i v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A coproduct summand is a retract when equality of indices is decidable. -/
noncomputable def Sigma.summandRetractOfDecidable {ι : Type i} [DecidableEq ι]
    (F : ι → C) [HasCoproduct F] (i : ι) : Retract (F i) (∐ F) where
  i := Sigma.ι F i
  r := Sigma.π F i
  retract := Sigma.ι_π_eq_id F i

/-- Every object in an indexed coproduct is a retract of the coproduct. -/
@[stacks 0G21 "coproduct summand retract"]
noncomputable def Sigma.summandRetract {ι : Type i}
    (F : ι → C) [HasCoproduct F] (i : ι) : Retract (F i) (∐ F) :=
  @Sigma.summandRetractOfDecidable C _ _ ι (Classical.decEq ι) F _ i

end CategoryTheory.Limits
