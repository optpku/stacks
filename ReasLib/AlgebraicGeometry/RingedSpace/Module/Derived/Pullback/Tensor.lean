module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TensorProduct
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived pullback and tensor

The public ringed-space interface records the pullback--tensor comparison as a proposition-valued
existence theorem.  This keeps deferred proof data out of the canonical data layer while giving
downstream developments one stable statement to instantiate.  Both pullback additivity and its
strong-monoidal structure are supplied by the canonical ringed-space owners.
-/

open AlgebraicGeometry CategoryTheory ComplexShape
open scoped RingedSpaceDerivedPullback RingedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Pullback

variable {X Y : RingedSpace.{u}}

/-- Stacks 079U: derived pullback commutes with the canonical fixed-right derived tensor. -/
@[stacks 079U "derived pullback--tensor comparison"]
theorem existsTensorIso
    (f : X ⟶ Y) (L : ModuleDerived Y) :
    ∃ τ :
      derivedTensorProduct L ⋙ modulePullbackDerived f ⟶
        modulePullbackDerived f ⋙
          derivedTensorProduct ((modulePullbackDerived f).obj L),
      IsIso τ := sorry

/-- The source counit for the pullback--tensor comparison, expressed through the canonical
fixed-right derived-tensor counit. -/
@[stacks 079U "derived pullback--tensor source counit"]
abbrev sourceCounit
    (f : X ⟶ Y) (L : ModuleDerived Y) :
    (DerivedCategory.Qh :
        HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y) ⋙
        (derivedTensorProduct L ⋙ modulePullbackDerived f) ⟶
      derivedTensorSourceFunctor L ⋙ modulePullbackDerived f :=
  (Functor.associator
      (DerivedCategory.Qh :
        HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y)
      (derivedTensorProduct L)
      (modulePullbackDerived f)).hom ≫
    Functor.whiskerRight (derivedTensorProductCounit L) (modulePullbackDerived f)

/-- The target counit for the pullback--tensor comparison. -/
@[stacks 079U "derived pullback--tensor target counit"]
abbrev targetCounit
    (f : X ⟶ Y) (L : ModuleDerived Y) :
    (DerivedCategory.Qh :
        HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y) ⋙
        (modulePullbackDerived f ⋙
          derivedTensorProduct ((modulePullbackDerived f).obj L)) ⟶
      modulePullbackToDerived f ⋙
        derivedTensorProduct ((modulePullbackDerived f).obj L) :=
  (Functor.associator
      (DerivedCategory.Qh :
        HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y)
      (modulePullbackDerived f)
      (derivedTensorProduct ((modulePullbackDerived f).obj L))).hom ≫
    Functor.whiskerRight
      ((modulePullbackToDerived f).totalLeftDerivedCounit
        (DerivedCategory.Qh :
          HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y)
        (ModuleQis Y))
      (derivedTensorProduct ((modulePullbackDerived f).obj L))

/-- Stacks 079U: the comparison can be chosen to make the canonical counit square commute. -/
@[stacks 079U "derived pullback--tensor counit square"]
theorem existsTensorIso_commSq
    (f : X ⟶ Y) (Kq : HomotopyCategory (Modules Y) (up ℤ)) (L : ModuleDerived Y) :
    ∃ τ :
      derivedTensorProduct L ⋙ modulePullbackDerived f ⟶
        modulePullbackDerived f ⋙
          derivedTensorProduct ((modulePullbackDerived f).obj L),
      ∃ σ :
        derivedTensorSourceFunctor L ⋙ modulePullbackDerived f ⟶
          modulePullbackToDerived f ⋙
            derivedTensorProduct ((modulePullbackDerived f).obj L),
        IsIso τ ∧
          CommSq
            ((Functor.whiskerLeft
              (DerivedCategory.Qh :
                HomotopyCategory (Modules Y) (up ℤ) ⥤ ModuleDerived Y) τ).app Kq)
            ((sourceCounit f L).app Kq)
            ((targetCounit f L).app Kq)
            (σ.app Kq) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Pullback

end
