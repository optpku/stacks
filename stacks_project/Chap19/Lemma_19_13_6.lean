module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.Preservation
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.HomotopyLimit.Grothendieck
import StacksCheckRecall

@[expose] public section

/-!
# Derived Limits of Sequential Inverse Systems

Lemma 19.13.6 is now owned by the neutral derived-limit API. This chapter file remains a
compatibility entry point for the historical chapter path.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB u₁ v₁ u₂ v₂

-- Lemma 19.13.6 is the shared preservation theorem below, shown with its full source-shaped
-- preservation statement.
@[stacks 08U1 "derived-limit preservation"] #check
  fun (A : Type u₁) (B : Type u₂)
      [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
      [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
      (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
      [HasCountableProducts B] [CountableAB4Star B]
      [PreservesLimitsOfShape (Discrete ℕ) F]
      {Ksys : SequentialInverseSystem (DerivedCategory A)} {K : DerivedCategory A}
      (hK : HomotopyLimit.IsOf Ksys K) ↦
    (Functor.RightDerived.KInjective.preservesHomotopyLimit F hK :
      HomotopyLimit.IsOf
        (Ksys ⋙ Functor.RightDerived.KInjective.functor F)
        ((Functor.RightDerived.KInjective.functor F).obj K))

-- The stagewise homotopy-limit model is a reusable companion, not a second source clause.
#check
  @CategoryTheory.DerivedLimit.Stage.isHomotopyLimit

-- The functorial stagewise tower is available for downstream naturality arguments.
#check @CategoryTheory.DerivedLimit.Stage.towerFunctor
