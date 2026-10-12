/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.PrincipalSeg
public import Mathlib.Order.Interval.Set.InitialSeg

/-!
# Limits over the strict predecessors of an inverse-system stage

For an inverse system indexed by a partially ordered type, this file names the restriction to
the strict predecessors of a stage and the canonical comparison from that stage to the limit of
the restricted system.  The construction is independent of additive or homological structure.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe v u w

namespace CategoryTheory.Functor

variable {J : Type u} [PartialOrder J]
variable {C : Type v} [Category.{w} C]

/-- The restriction of an inverse system to the strict predecessors of `β`. -/
abbrev predecessorDiagram (K : Jᵒᵖ ⥤ C) (β : J) : (Set.Iio β)ᵒᵖ ⥤ C :=
  (Set.principalSegIio β).monotone.functor.op ⋙ K

/-- The canonical cone from an inverse-system stage to its strict-predecessor diagram. -/
noncomputable def predecessorCone (K : Jᵒᵖ ⥤ C) (β : J) :
    Cone (K.predecessorDiagram β) :=
  coneOfCoconeRightOp <|
    show Cocone (K.predecessorDiagram β).rightOp from
      (Set.principalSegIio β).cocone K.rightOp

/-- The canonical comparison from a stage of an inverse system to the limit over all its strict
predecessors. -/
noncomputable def predecessorLimitComparison (K : Jᵒᵖ ⥤ C) (β : J)
    [HasLimit (K.predecessorDiagram β)] :
    K.obj (op β) ⟶ limit (K.predecessorDiagram β) :=
  limit.lift _ (predecessorCone K β)

/-- Projecting the predecessor-limit comparison to `γ < β` recovers the transition from `β`
to `γ`. -/
@[reassoc (attr := simp)]
theorem predecessorLimitComparison.π (K : Jᵒᵖ ⥤ C) (β : J)
    [HasLimit (K.predecessorDiagram β)] (γ : Set.Iio β) :
    K.predecessorLimitComparison β ≫ limit.π (K.predecessorDiagram β) (op γ) =
      K.map (homOfLE γ.2.le).op := sorry

/-- The predecessor-limit comparison is the unique map whose projections are the inverse-system
transition maps from the given stage. -/
theorem predecessorLimitComparison.existsUnique (K : Jᵒᵖ ⥤ C) (β : J)
    [HasLimit (K.predecessorDiagram β)] :
    ∃! f : K.obj (op β) ⟶ limit (K.predecessorDiagram β),
      ∀ γ : Set.Iio β,
        f ≫ limit.π (K.predecessorDiagram β) (op γ) =
          K.map (homOfLE γ.2.le).op := sorry

/- Data audit (mathlib 4.32): `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound` for `predecessorDiagram`, `predecessorCone`, and
`predecessorLimitComparison`; none of these data owners depends on the deferred specification
theorems. -/

end CategoryTheory.Functor
