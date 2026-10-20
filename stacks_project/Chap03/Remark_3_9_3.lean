module

public import ReasLib.AlgebraicGeometry.Scheme.Reflection
import StacksCheckRecall

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

/- Remark 3.9.3 (000O). Unary reflection of the formula expressing that an
object is a scheme is insufficient. Applying reflection jointly to the formula
expressing that `Y` is the reduction of `X` and its existential projection in
`X` yields the closure of `Sch_α` under reductions. -/

@[stacks 000O] #check (AlgebraicGeometry.Scheme.reduction_mem_of_joint_reflection :
    ∀ {P : ObjectProperty Scheme.{u}}
    (red red_bounded : Scheme.{u} → Scheme.{u} → Prop)
    (hasRed hasRed_bounded : Scheme.{u} → Prop)
    (red_spec : ∀ X Y, red X Y ↔ Y = Scheme.reduction X)
    (hasRed_spec : ∀ X, hasRed X ↔ ∃ Y, red X Y)
    (red_reflection : ∀ {X Y}, P X →
      (red_bounded X Y ↔ red X Y ∧ P Y))
    (hasRed_reflection : ∀ {X}, P X →
      (hasRed_bounded X ↔ hasRed X))
    (hasRed_bounded_spec : ∀ X, hasRed_bounded X ↔ ∃ Y, red_bounded X Y)
    {X : Scheme.{u}} (hX : P X), P (Scheme.reduction X))
