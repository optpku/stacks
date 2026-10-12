/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Split
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical splitting of strict co-Grothendieck projections

This leaf owns the canonical split cleavage on the co-Grothendieck projection of a strict
contravariant `Cat`-valued functor.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]

namespace Pseudofunctor.CoGrothendieck

/-- The canonical split cleavage on the co-Grothendieck projection of a strict contravariant
`Cat`-valued functor. Its selected lifts are mathlib's explicit co-Grothendieck cartesian lifts;
only their strict identity and composition laws remain proof obligations. -/
@[stacks 02XW "canonical splitting of a strict co-Grothendieck projection"]
def splitCleavage (F : Cᵒᵖ ⥤ Cat.{v₂, u₂}) :
    (forget F.toPseudofunctor').SplitCleavage where
  toCleavage :=
    { lift := fun {x V} f =>
        { source := domainCartesianLift x.fiber f
          hom := cartesianLift x.fiber f
          isStronglyCartesian := isStronglyCartesian_homCartesianLift x.fiber f } }
  isSplit :=
    { reindexObj_id := sorry
      cartesianHom_id := sorry
      reindexObj_comp := sorry
      cartesianHom_comp := sorry }

/-- The co-Grothendieck projection of a strict `Cat`-valued presheaf is split fibred by its
canonical selected cartesian lifts. -/
@[stacks 02XW "canonical split-fibred structure of a strict co-Grothendieck projection"]
instance isFiberedSplit (F : Cᵒᵖ ⥤ Cat.{v₂, u₂}) :
    Functor.IsFibered.Split (forget F.toPseudofunctor') where
  exists_splitCleavage := ⟨splitCleavage F⟩

end Pseudofunctor.CoGrothendieck

end CategoryTheory
