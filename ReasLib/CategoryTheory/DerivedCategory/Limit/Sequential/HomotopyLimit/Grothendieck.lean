module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.DerivedFunctor.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Tower
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Stagewise Homotopy Limits in Grothendieck Abelian Categories

@stack 08U1

The total right derived inverse-limit functor is a homotopy limit of the
stagewise evaluation tower. The result uses the presentation-independent
`HomotopyLimit.IsOf` predicate and therefore selects no product instance.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wSys u v

namespace CategoryTheory.DerivedLimit.Stage

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

/-- The total right derived inverse limit is a sequential homotopy limit of the stagewise
evaluation tower. -/
@[stacks 08U1 "stagewise homotopy-limit model"]
theorem isHomotopyLimit
    [IsGrothendieckAbelian.{w} A]
    [IsGrothendieckAbelian.{w} (SequentialInverseSystem A)]
    [HasLimitsOfShape ℕᵒᵖ A]
    [HasCountableProducts A] [CountableAB4Star A]
    [PreservesLimitsOfShape (Discrete ℕ) (lim : SequentialInverseSystem A ⥤ A)]
    (K : DerivedCategory (SequentialInverseSystem A)) :
    HomotopyLimit.IsOf (tower K) ((DerivedLimit.functor A).obj K) := sorry

end CategoryTheory.DerivedLimit.Stage
