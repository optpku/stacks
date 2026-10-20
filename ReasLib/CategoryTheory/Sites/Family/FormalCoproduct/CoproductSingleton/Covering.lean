module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton.Over
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Basis

/-!
# Covering singleton replacements

This module records when replacing a finite fixed-target covering family by the singleton family
on the coproduct of its sources preserves the covering condition.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.Limits.FormalCoproduct.IsCovering

variable {C : Type u} [Category.{v} C]

/-- The singleton family on the coproduct of the sources of a finite covering family is covering
over the same target. -/
theorem coproductSingleton
    (J : GrothendieckTopology C) {U : C}
    (K : FormalCoproduct.{w} (CategoryTheory.Over U)) [Finite K.I]
    [HasCoproduct (fun i ↦ (K.obj i).left)]
    (hK : FormalCoproduct.IsCovering J.toPrecoverage K) :
    FormalCoproduct.IsCovering J.toPrecoverage
      (FormalCoproduct.Over.coproductSingleton K) := sorry

end CategoryTheory.Limits.FormalCoproduct.IsCovering
